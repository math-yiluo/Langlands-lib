import Langlands.Algebra.BinaryElementary
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! The actual quotient of binary matrix units by elementary matrices. -/

namespace Langlands.BinaryElementary

universe u

section Ring

variable {D : Type u} [Ring D]

/-- Diagonal units preserve the elementary subgroup under conjugation. -/
theorem diagonal_conj_mem (a b : Dˣ) {n : GL₂ D} (hn : n ∈ elementary D) :
    diagonal a b * n * (diagonal a b)⁻¹ ∈ elementary D := by
  refine Subgroup.closure_induction (fun x hx => ?_) ?_
    (fun x y _ _ ihx ihy => ?_) (fun x _ ihx => ?_) hn
  · rcases hx with ⟨x, rfl⟩ | ⟨x, rfl⟩
    · rw [diagonal_conj_upper]
      exact upper_mem _
    · rw [diagonal_conj_lower]
      exact lower_mem _
  · simpa only [mul_one, mul_inv_cancel] using (elementary D).one_mem
  · rw [← conj_mul]
    exact (elementary D).mul_mem ihx ihy
  · rw [← conj_inv]
    exact (elementary D).inv_mem ihx

/-- A scaled signed interchange is a product of three elementary matrices. -/
theorem diagonal_mul_weyl (a : Dˣ) :
    diagonal a a⁻¹ * weyl =
      upper (a : D) * lower (-((a⁻¹ : Dˣ) : D)) * upper (a : D) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, mul_assoc]

/-- A diagonal unit and its inverse form an elementary binary matrix. -/
theorem diagonal_inverse_mem (a : Dˣ) : diagonal a a⁻¹ ∈ elementary D := by
  have h : diagonal a a⁻¹ * weyl ∈ elementary D := by
    rw [diagonal_mul_weyl]
    exact (elementary D).mul_mem
      ((elementary D).mul_mem (upper_mem _) (lower_mem _)) (upper_mem _)
  simpa using (elementary D).mul_mem h ((elementary D).inv_mem weyl_mem)

@[simp] theorem diagonal_one : diagonal (1 : Dˣ) 1 = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp

end Ring

section DivisionRing

variable {D : Type u} [DivisionRing D]

/-- Over a division ring, the binary elementary subgroup is normal. -/
instance elementary_normal : (elementary D).Normal where
  conj_mem n hn g := by
    obtain ⟨e, f, a, b, he, hf, rfl⟩ := exists_elementary_diagonal_elementary g
    have hf' : f * n * f⁻¹ ∈ elementary D :=
      (elementary D).mul_mem ((elementary D).mul_mem hf hn) ((elementary D).inv_mem hf)
    have hd := diagonal_conj_mem a b hf'
    have he' := (elementary D).mul_mem ((elementary D).mul_mem he hd)
      ((elementary D).inv_mem he)
    simpa [mul_inv_rev, mul_assoc] using he'

/-- The quotient by the actual elementary subgroup, with its induced group law. -/
def ElementaryQuotient (D : Type u) [DivisionRing D] := GL₂ D ⧸ elementary D

instance : Group (ElementaryQuotient D) :=
  inferInstanceAs (Group (GL₂ D ⧸ elementary D))

/-- The canonical homomorphism from binary matrix units to their quotient. -/
def quotientMap : GL₂ D →* ElementaryQuotient D := QuotientGroup.mk' (elementary D)

theorem quotientMap_surjective : Function.Surjective (quotientMap (D := D)) :=
  QuotientGroup.mk'_surjective _

@[simp] theorem quotientMap_eq_one_iff (g : GL₂ D) :
    quotientMap g = 1 ↔ g ∈ elementary D := QuotientGroup.eq_one_iff g

/-- Every quotient class has an actual diagonal representative. -/
theorem exists_diagonal_representative (q : ElementaryQuotient D) :
    ∃ a b : Dˣ, quotientMap (diagonal a b) = q := by
  obtain ⟨g, rfl⟩ := quotientMap_surjective q
  obtain ⟨e, f, a, b, he, hf, rfl⟩ := exists_elementary_diagonal_elementary g
  refine ⟨a, b, ?_⟩
  simp only [map_mul, (quotientMap_eq_one_iff e).mpr he,
    (quotientMap_eq_one_iff f).mpr hf, one_mul, mul_one]

/-- Either diagonal position gives the same class for a coefficient unit. -/
theorem quotientMap_diagonal_one_swap (a : Dˣ) :
    quotientMap (diagonal a 1) = quotientMap (diagonal 1 a) := by
  calc
    quotientMap (diagonal a 1) =
        quotientMap (diagonal a a⁻¹ * diagonal 1 a) := by
      rw [diagonal_mul]
      simp
    _ = quotientMap (diagonal 1 a) := by
      rw [map_mul, (quotientMap_eq_one_iff _).mpr (diagonal_inverse_mem a), one_mul]

/-- The ordered product of the two diagonal entries represents the same class. -/
theorem quotientMap_diagonal (a b : Dˣ) :
    quotientMap (diagonal a b) = quotientMap (diagonal (a * b) 1) := by
  calc
    quotientMap (diagonal a b) =
        quotientMap (diagonal a 1) * quotientMap (diagonal 1 b) := by
      rw [← map_mul, diagonal_mul]
      simp
    _ = quotientMap (diagonal a 1) * quotientMap (diagonal b 1) := by
      rw [quotientMap_diagonal_one_swap b]
    _ = quotientMap (diagonal (a * b) 1) := by
      rw [← map_mul, diagonal_mul, one_mul]

/-- Coefficient units map to their first-diagonal classes. -/
def unitClass : Dˣ →* ElementaryQuotient D where
  toFun a := quotientMap (diagonal a 1)
  map_one' := by rw [diagonal_one, map_one]
  map_mul' a b := by rw [← map_mul, diagonal_mul, one_mul]

theorem unitClass_surjective : Function.Surjective (unitClass (D := D)) := by
  intro q
  obtain ⟨a, b, h⟩ := exists_diagonal_representative q
  exact ⟨a * b, (quotientMap_diagonal a b).symm.trans h⟩

/-- Quotient multiplication commutes even when coefficient multiplication does not. -/
theorem quotient_mul_comm (x y : ElementaryQuotient D) : x * y = y * x := by
  obtain ⟨a, rfl⟩ := unitClass_surjective x
  obtain ⟨b, rfl⟩ := unitClass_surjective y
  change quotientMap (diagonal a 1) * quotientMap (diagonal b 1) =
    quotientMap (diagonal b 1) * quotientMap (diagonal a 1)
  rw [quotientMap_diagonal_one_swap b, ← map_mul, ← map_mul]
  congr 1
  simp [diagonal_mul]

instance : CommGroup (ElementaryQuotient D) where
  mul_comm := quotient_mul_comm

end DivisionRing

end Langlands.BinaryElementary
