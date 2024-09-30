-- This module serves as the root of the `First` library.
-- Import modules here that should be built as part of the library.
import First.Basic
import Mathlib

example : ∀ m n : Nat, Even n → Even (m * n) := fun m n ⟨k, (hk : n = k + k)⟩ ↦
  have hmn : m * n = m * k + m * k := by rw [hk, Nat.mul_add]
  show ∃ l, m * n = l + l from ⟨_, hmn⟩

example : ∀ m n : Nat, Even n → Even (m * n) := by
  rintro m n ⟨k, hk⟩
  use m * k
  rw [hk]
  ring

example (a b c : ℝ) : a * b * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc b a c]

example (a b c : ℝ ) : a * (b * c) = b * (c * a) := by
  rw [mul_comm, mul_assoc]

example (a b c : ℝ ) : a * (b * c) = b * (c * a) := by
  rw [mul_comm a]
  rw [mul_assoc b]


example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a+b)*(a+b) = a*a+a*b+(b*a + b*b) := by
      rw [add_mul, mul_add, mul_add]
    _= a*a+(a*b+a*b)+b*b := by
      rw[mul_comm b a, ← add_assoc, add_assoc (a*a)]
    _= a*a+2*(a*b)+b*b := by
      rw[← two_mul]

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      rw [mul_add, add_mul, add_mul]
    _ = a * a + (b * a + a * b) + b * b := by
      rw [← add_assoc, add_assoc (a*a)]
    _ = a * a + 2 * (a * b) + b * b := by
      rw [mul_comm b a, ← two_mul]

variable (a b c : ℝ)
example (a b : ℝ ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  calc
    (a+b)*(a-b) = a*a +b*a -a*b -b*b := by
      rw [mul_sub, add_mul, add_mul, ← sub_sub]
    _= a*a-b*b := by
      rw [mul_comm b a, ← add_sub, sub_self, add_zero]
    _= a^2-b^2 := by
      rw [← pow_two, ← pow_two]

#check pow_two a
#check mul_sub a b c
#check add_mul a b c
#check add_sub a b c
#check sub_sub a b c
#check add_zero a
