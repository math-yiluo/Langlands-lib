import Langlands.Algebra.BinaryElementaryQuotient
import Mathlib.GroupTheory.Abelianization.Defs

/-! A concrete binary determinant with values in the abelianized coefficient units. -/

noncomputable section

namespace Langlands.BinaryElementary

universe u

variable {D : Type u} [DivisionRing D]

local instance : DecidableEq D := Classical.decEq D

namespace Dieudonne

/-- The class of a nonzero coefficient; its arbitrary value at zero is unused. -/
def coefficientClass (x : D) : Abelianization Dˣ :=
  if hx : x = 0 then 1 else Abelianization.of (Units.mk0 x hx)

theorem coefficientClass_of_ne_zero (x : D) (hx : x ≠ 0) :
    coefficientClass x = Abelianization.of (Units.mk0 x hx) := by
  simp [coefficientClass, hx]

@[simp] theorem coefficientClass_one : coefficientClass (1 : D) = 1 := by
  simp [coefficientClass]

@[simp] theorem coefficientClass_unit (a : Dˣ) :
    coefficientClass (a : D) = Abelianization.of a := by
  simp [coefficientClass, a.ne_zero]

theorem coefficientClass_mul {x y : D} (hx : x ≠ 0) (hy : y ≠ 0) :
    coefficientClass (x * y) = coefficientClass x * coefficientClass y := by
  simp [coefficientClass, hx, hy, mul_ne_zero hx hy]

theorem coefficientClass_inv (x : D) :
    coefficientClass x⁻¹ = (coefficientClass x)⁻¹ := by
  by_cases hx : x = 0
  · simp [hx, coefficientClass]
  · rw [coefficientClass_of_ne_zero _ (inv_ne_zero hx), coefficientClass_of_ne_zero _ hx]
    have h : Units.mk0 x⁻¹ (inv_ne_zero hx) = (Units.mk0 x hx)⁻¹ :=
      Units.ext rfl
    rw [h, map_inv]

/-- The ordered Schur complement at the top-left pivot. -/
def schur (g : GL₂ D) : D := g.val 1 1 - g.val 1 0 * (g.val 0 0)⁻¹ * g.val 0 1

/-- The corresponding complement when the lower-left entry is the pivot. -/
def coSchur (g : GL₂ D) : D := g.val 0 1 - g.val 0 0 * (g.val 1 0)⁻¹ * g.val 1 1

theorem schur_ne_zero (g : GL₂ D) (ha : g.val 0 0 ≠ 0) : schur g ≠ 0 := by
  let e := lower (-g.val 1 0 * (g.val 0 0)⁻¹)
  let f := upper (-(g.val 0 0)⁻¹ * g.val 0 1)
  have hk : (e * g * f).val = !![g.val 0 0, 0; 0, schur g] := eliminate g.val ha
  intro hs
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) D => M 1 1)
    (e * g * f).mul_inv
  rw [hk] at h
  simp [Matrix.mul_apply, Fin.sum_univ_two, hs] at h

theorem coSchur_ne_zero (g : GL₂ D) (hc : g.val 1 0 ≠ 0) : coSchur g ≠ 0 := by
  have hp : (weyl * g).val 0 0 ≠ 0 := by
    simpa [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two] using hc
  have h := schur_ne_zero (weyl * g) hp
  have heq : schur (weyl * g) = -(coSchur g) := by
    simp [schur, coSchur, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two,
      sub_eq_add_neg, add_comm]
  rw [heq, neg_ne_zero] at h
  exact h

theorem coSchur_eq (g : GL₂ D) (ha : g.val 0 0 ≠ 0) (hc : g.val 1 0 ≠ 0) :
    coSchur g = -g.val 0 0 * (g.val 1 0)⁻¹ * schur g := by
  simp [schur, coSchur, sub_eq_add_neg, mul_add, mul_assoc, ha, hc, add_comm]

/-- The two pivot formulas agree after abelianizing coefficient units. -/
theorem pivot_formula_eq (g : GL₂ D) (ha : g.val 0 0 ≠ 0) (hc : g.val 1 0 ≠ 0) :
    coefficientClass (g.val 0 0) * coefficientClass (schur g) =
      coefficientClass (-g.val 1 0) * coefficientClass (coSchur g) := by
  have hs := schur_ne_zero g ha
  have ht := coSchur_ne_zero g hc
  rw [← coefficientClass_mul ha hs, ← coefficientClass_mul (neg_ne_zero.mpr hc) ht]
  have h : -g.val 1 0 * coSchur g =
      g.val 1 0 * g.val 0 0 * (g.val 1 0)⁻¹ * schur g := by
    rw [coSchur_eq g ha hc]
    simp [mul_assoc]
  rw [h, coefficientClass_mul (mul_ne_zero (mul_ne_zero hc ha) (inv_ne_zero hc)) hs,
    coefficientClass_mul (mul_ne_zero hc ha) (inv_ne_zero hc),
    coefficientClass_mul hc ha, coefficientClass_inv, coefficientClass_mul ha hs]
  simp [mul_comm, mul_assoc]

/-- The concrete two-pivot binary determinant as a function. -/
def value (g : GL₂ D) : Abelianization Dˣ :=
  if g.val 0 0 = 0 then
    coefficientClass (-g.val 1 0) * coefficientClass (coSchur g)
  else
    coefficientClass (g.val 0 0) * coefficientClass (schur g)

theorem value_of_top (g : GL₂ D) (ha : g.val 0 0 ≠ 0) :
    value g = coefficientClass (g.val 0 0) * coefficientClass (schur g) := by
  simp [value, ha]

theorem value_of_bottom (g : GL₂ D) (hc : g.val 1 0 ≠ 0) :
    value g = coefficientClass (-g.val 1 0) * coefficientClass (coSchur g) := by
  by_cases ha : g.val 0 0 = 0
  · simp [value, ha]
  · rw [value_of_top g ha, pivot_formula_eq g ha hc]

@[simp] theorem value_one : value (1 : GL₂ D) = 1 := by
  simp [value, schur]

/-- Adding a multiple of the first row to the second preserves the value. -/
theorem value_lower_mul (x : D) (g : GL₂ D) :
    value (lower x * g) = value g := by
  by_cases ha : g.val 0 0 = 0
  · simp [value, coSchur, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, ha]
  · have ha' : (lower x * g).val 0 0 ≠ 0 := by
      simpa [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two] using ha
    rw [value_of_top _ ha', value_of_top _ ha]
    have hs : schur (lower x * g) = schur g := by
      simp [schur, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two,
        add_mul, mul_assoc, ha, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    simp [hs, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]

/-- Adding a multiple of the second row to the first preserves the value. -/
theorem value_upper_mul (x : D) (g : GL₂ D) :
    value (upper x * g) = value g := by
  by_cases hc : g.val 1 0 = 0
  · have ha : g.val 0 0 ≠ 0 := (firstColumn_ne_zero g).resolve_right (not_not.mpr hc)
    have ha' : (upper x * g).val 0 0 ≠ 0 := by
      simpa [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hc] using ha
    rw [value_of_top _ ha', value_of_top _ ha]
    simp [schur, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hc]
  · have hc' : (upper x * g).val 1 0 ≠ 0 := by
      simpa [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two] using hc
    rw [value_of_bottom _ hc', value_of_bottom _ hc]
    have ht : coSchur (upper x * g) = coSchur g := by
      simp [coSchur, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two,
        add_mul, mul_assoc, hc, sub_eq_add_neg, add_comm, add_assoc]
    simp [ht, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]

/-- Every actual elementary matrix preserves the value on the left. -/
theorem value_elementary_mul {e : GL₂ D} (he : e ∈ elementary D) (g : GL₂ D) :
    value (e * g) = value g := by
  have h : ∀ h ∈ elementary D, ∀ k : GL₂ D, value (h * k) = value k := by
    intro h hh
    refine Subgroup.closure_induction (fun z hz => ?_) ?_
      (fun a b _ _ iha ihb => ?_) (fun a _ iha => ?_) hh
    · rcases hz with ⟨x, rfl⟩ | ⟨x, rfl⟩
      · exact value_upper_mul x
      · exact value_lower_mul x
    · intro k
      simp
    · intro k
      rw [mul_assoc, iha, ihb]
    · intro k
      have ht := iha (a⁻¹ * k)
      simpa using ht.symm
  exact h e he g

/-- Normality also gives invariance under elementary multiplication on the right. -/
theorem value_mul_elementary {e : GL₂ D} (he : e ∈ elementary D) (g : GL₂ D) :
    value (g * e) = value g := by
  have hc := (inferInstance : (elementary D).Normal).conj_mem e he g
  simpa [mul_assoc] using value_elementary_mul hc g

@[simp] theorem value_diagonal (a b : Dˣ) :
    value (diagonal a b) = Abelianization.of a * Abelianization.of b := by
  simp [value, schur, a.ne_zero]

/-- The concrete pivot formula descends to the actual elementary quotient. -/
def quotientValue : ElementaryQuotient D → Abelianization Dˣ :=
  Quotient.lift value (by
    intro g h hrel
    have he : g⁻¹ * h ∈ elementary D := QuotientGroup.leftRel_apply.mp hrel
    simpa using (value_mul_elementary he g).symm)

@[simp] theorem quotientValue_quotientMap (g : GL₂ D) :
    quotientValue (quotientMap g) = value g := rfl

@[simp] theorem quotientValue_unitClass (a : Dˣ) :
    quotientValue (unitClass a) = Abelianization.of a := by
  change value (diagonal a 1) = Abelianization.of a
  simp

/-- The diagonal-unit map factors through coefficient abelianization. -/
def abelianizedUnitClass : Abelianization Dˣ →* ElementaryQuotient D :=
  Abelianization.lift unitClass

@[simp] theorem abelianizedUnitClass_of (a : Dˣ) :
    abelianizedUnitClass (Abelianization.of a) = unitClass a := rfl

/-- The pivot formula recovers each coefficient class from its diagonal image. -/
theorem quotientValue_abelianizedUnitClass (x : Abelianization Dˣ) :
    quotientValue (abelianizedUnitClass x) = x := by
  refine QuotientGroup.induction_on x ?_
  intro a
  change quotientValue (abelianizedUnitClass (Abelianization.of a)) =
    Abelianization.of a
  simp

theorem abelianizedUnitClass_bijective :
    Function.Bijective (abelianizedUnitClass (D := D)) := by
  constructor
  · exact Function.LeftInverse.injective quotientValue_abelianizedUnitClass
  · intro q
    obtain ⟨a, rfl⟩ := unitClass_surjective q
    exact ⟨Abelianization.of a, abelianizedUnitClass_of a⟩

/-- The actual binary elementary quotient is the abelianization of coefficient units. -/
def quotientEquiv : ElementaryQuotient D ≃* Abelianization Dˣ :=
  (MulEquiv.ofBijective abelianizedUnitClass abelianizedUnitClass_bijective).symm

theorem quotientEquiv_eq_quotientValue (q : ElementaryQuotient D) :
    quotientEquiv q = quotientValue q := by
  obtain ⟨x, rfl⟩ := abelianizedUnitClass_bijective.surjective q
  exact (quotientEquiv.apply_symm_apply x).trans
    (quotientValue_abelianizedUnitClass x).symm

/-- The binary Dieudonné determinant, with no supplied determinant or splitting data. -/
def determinant : GL₂ D →* Abelianization Dˣ :=
  quotientEquiv.toMonoidHom.comp quotientMap

theorem determinant_eq_value (g : GL₂ D) : determinant g = value g := by
  exact quotientEquiv_eq_quotientValue (quotientMap g)

@[simp] theorem determinant_diagonal (a b : Dˣ) :
    determinant (diagonal a b) = Abelianization.of a * Abelianization.of b := by
  rw [determinant_eq_value, value_diagonal]

/-- Multiplicativity of the explicit two-pivot formula follows from the quotient equivalence. -/
theorem value_mul (g h : GL₂ D) : value (g * h) = value g * value h := by
  simp only [← determinant_eq_value, map_mul]

/-- The determinant has exactly the actual elementary subgroup as kernel. -/
theorem determinant_eq_one_iff (g : GL₂ D) :
    determinant g = 1 ↔ g ∈ elementary D := by
  change quotientEquiv (quotientMap g) = 1 ↔ _
  rw [quotientEquiv.map_eq_one_iff, quotientMap_eq_one_iff]

theorem determinant_surjective : Function.Surjective (determinant (D := D)) :=
  quotientEquiv.surjective.comp quotientMap_surjective

theorem ker_determinant : (determinant (D := D)).ker = elementary D := by
  exact Subgroup.ext determinant_eq_one_iff

/-- A coefficient diagonal is elementary exactly when its unit is a product of commutators. -/
theorem unitClass_eq_one_iff (a : Dˣ) :
    unitClass a = 1 ↔ a ∈ commutator Dˣ := by
  have h : quotientEquiv (unitClass a) = Abelianization.of a := by
    change determinant (diagonal a 1) = _
    simp
  rw [← quotientEquiv.map_eq_one_iff, h]
  change a ∈ (Abelianization.of : Dˣ →* Abelianization Dˣ).ker ↔ _
  rw [Abelianization.ker_of]

theorem diagonal_one_mem_iff (a : Dˣ) :
    diagonal a 1 ∈ elementary D ↔ a ∈ commutator Dˣ := by
  rw [← quotientMap_eq_one_iff]
  exact unitClass_eq_one_iff a

end Dieudonne

end Langlands.BinaryElementary
