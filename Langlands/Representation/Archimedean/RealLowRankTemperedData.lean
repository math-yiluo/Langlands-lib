import Langlands.Representation.Archimedean.RealRankOneStandardModule
import Langlands.Representation.Archimedean.RealTemperedCommutantReduction

/-!
# Form and scalar-commutant data in ranks zero and one

Evaluation equivalences construct the exact form and commutant inputs for
real standard modules of rank at most one.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct Matrix

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

namespace RealLowRankTemperedData

open RealTemperedCommutantReduction

section OneDimensional

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Every endomorphism of a complex line is scalar. -/
theorem endomorphism_scalar (e : V ≃ₗ[ℂ] ℂ) (E : V →ₗ[ℂ] V) :
    ∃ c : ℂ, ∀ v : V, E v = c • v := by
  refine ⟨e (E (e.symm 1)), fun v => ?_⟩
  have hv : v = e v • e.symm 1 := by
    apply e.injective
    simp
  have hE : E v = e v • E (e.symm 1) :=
    (congrArg E hv).trans (map_smul E _ _)
  apply e.injective
  rw [hE, map_smul, map_smul, smul_eq_mul, smul_eq_mul, mul_comm]

/-- The standard linear-first form on a complex line, pulled back along `e`. -/
def evalForm (e : V ≃ₗ[ℂ] ℂ) : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ where
  toFun v :=
    { toFun := fun w => e v * star (e w)
      map_add' := by
        intro w z
        simp only [map_add, star_add, mul_add]
      map_smul' := by
        intro c w
        simp [map_smul, mul_left_comm] }
  map_add' := by
    intro v w
    ext z
    change e (v + w) * star (e z) = e v * star (e z) + e w * star (e z)
    rw [map_add, add_mul]
  map_smul' := by
    intro c v
    ext w
    simp [map_smul, mul_assoc]

@[simp]
theorem evalForm_apply (e : V ≃ₗ[ℂ] ℂ) (v w : V) :
    evalForm e v w = e v * star (e w) := rfl

/-- The pulled-back form is diagonally anisotropic. -/
theorem evalForm_anisotropic (e : V ≃ₗ[ℂ] ℂ) (v : V)
    (h : evalForm e v v = 0) : v = 0 := by
  apply e.injective
  rw [map_zero]
  change e v * star (e v) = 0 at h
  rcases mul_eq_zero.mp h with h | h
  · exact h
  · exact star_eq_zero.mp h

end OneDimensional

/-- A linear equivalence to a complex line supplies the scalar commutant
for any actual compact and Lie actions. -/
theorem hasScalarCommutant_of_equiv (n : ℕ) (ds : List RealBlock)
    (e : KF n ds ≃ₗ[ℂ] ℂ) : HasScalarCommutant n ds := by
  intro E _ _
  exact endomorphism_scalar e E

/-- A complex-line realization with unitary compact character supplies the
exact form data. The Lie identity follows from scalarity of each operator. -/
theorem hasTemperedForm_of_equiv (n : ℕ) (ds : List RealBlock)
    (e : KF n ds ≃ₗ[ℂ] ℂ)
    (a : Matrix.unitaryGroup (Fin n) ℝ → ℂ)
    (ha : ∀ k, a k * star (a k) = 1)
    (hK : ∀ k v, e (realStandardRep n ds k v) = a k * e v) :
    HasTemperedForm n ds := by
  refine ⟨e.symm.injective.nontrivial, evalForm e, evalForm_anisotropic e, ?_, ?_⟩
  · intro k v w
    simp only [evalForm_apply, hK, star_mul]
    calc
      a k * e v * (star (e w) * star (a k)) =
          (a k * star (a k)) * (e v * star (e w)) := by ring
      _ = e v * star (e w) := by rw [ha, one_mul]
  · intro X
    obtain ⟨c, hc⟩ := endomorphism_scalar e (realStandardLie n ds (1 ⊗ₜ X))
    refine ⟨c + star c, fun v w => ?_⟩
    change e (realStandardLie n ds (1 ⊗ₜ X) v) * star (e w) +
      e v * star (e (realStandardLie n ds (1 ⊗ₜ X) w)) =
        (c + star c) * (e v * star (e w))
    simp only [hc, map_smul, smul_eq_mul, star_mul]
    ring

/-- The rank-zero actual compact action is trivial in evaluation coordinates. -/
theorem hasTemperedForm_zero : HasTemperedForm 0 [] := by
  apply hasTemperedForm_of_equiv 0 [] RealRankZeroStandardModule.evalEquiv (fun _ => 1)
  · intro k
    simp
  · intro k v
    change ((realStandardRep 0 [] k v :
      Langlands.GeneralLinear 0 ℝ → ℂ) 1) = 1 * (v : Langlands.GeneralLinear 0 ℝ → ℂ) 1
    rw [realStandardRep_apply_coe]
    change (v : Langlands.GeneralLinear 0 ℝ → ℂ) (1 * Unitary.toUnits k) = _
    have h : 1 * Unitary.toUnits k = (1 : Langlands.GeneralLinear 0 ℝ) :=
      Subsingleton.elim _ _
    rw [h, one_mul]

/-- The compact character of a rank-one standard module has absolute value one,
even when the real exponent of the character is nonzero. -/
theorem characterVector_unitary (d : RealCharacterData)
    (k : Matrix.unitaryGroup (Fin 1) ℝ) :
    RealRankOneStandardModule.characterVector d (Unitary.toUnits k) *
      star (RealRankOneStandardModule.characterVector d (Unitary.toUnits k)) = 1 := by
  have hk := Unitary.star_mul_self_of_mem (Matrix.det_of_mem_unitary k.2)
  rw [star_trivial] at hk
  have hcases := mul_self_eq_one_iff.mp hk
  unfold RealRankOneStandardModule.characterVector
  rw [d.character_eq]
  change (((((k : Matrix (Fin 1) (Fin 1) ℝ).det /
      |(k : Matrix (Fin 1) (Fin 1) ℝ).det| : ℝ) : ℂ) ^ d.parity.val) *
      ((|(k : Matrix (Fin 1) (Fin 1) ℝ).det| : ℝ) : ℂ) ^ d.exponent) *
    star (((((k : Matrix (Fin 1) (Fin 1) ℝ).det /
      |(k : Matrix (Fin 1) (Fin 1) ℝ).det| : ℝ) : ℂ) ^ d.parity.val) *
      ((|(k : Matrix (Fin 1) (Fin 1) ℝ).det| : ℝ) : ℂ) ^ d.exponent) = 1
  rcases hcases with h | h <;> rw [h] <;> simp [← mul_pow]

/-- A rank-one standard module has the exact required form data. -/
theorem hasTemperedForm_one (d : RealCharacterData) :
    HasTemperedForm 1 [.character d] := by
  apply hasTemperedForm_of_equiv 1 [.character d] (RealRankOneStandardModule.evalEquiv d)
    (fun k => RealRankOneStandardModule.characterVector d (Unitary.toUnits k))
    (characterVector_unitary d)
  intro k v
  change ((realStandardRep 1 [.character d] k v : RealRankOneStandardModule.G → ℂ) 1) =
    RealRankOneStandardModule.characterVector d (Unitary.toUnits k) *
      (v : RealRankOneStandardModule.G → ℂ) 1
  rw [realStandardRep_apply_coe]
  change (v : RealRankOneStandardModule.G → ℂ) (1 * Unitary.toUnits k) = _
  rw [one_mul]
  exact RealRankOneStandardModule.eval_formula d v.2.1.1 _

end RealLowRankTemperedData

/-- Both analytical prerequisite interfaces hold for every real standard
module of rank at most one. No equal-exponent hypothesis is needed. -/
def RealLowRankTemperedDataStatement : Prop :=
  ∀ (n : ℕ) (ds : List RealBlock), realRank ds = n → n ≤ 1 →
    RealTemperedCommutantReduction.HasTemperedForm n ds ∧
      RealTemperedCommutantReduction.HasScalarCommutant n ds

/-- The explicit evaluation realizations supply both low-rank prerequisites. -/
theorem realLowRankTemperedData : RealLowRankTemperedDataStatement := by
  intro n ds hr hn
  interval_cases n
  · rw [RealRankZeroStandardModule.eq_nil_of_realRank_eq_zero ds hr]
    exact ⟨RealLowRankTemperedData.hasTemperedForm_zero,
      RealLowRankTemperedData.hasScalarCommutant_of_equiv 0 []
        RealRankZeroStandardModule.evalEquiv⟩
  · obtain ⟨d, rfl⟩ := RealRankOneStandardModule.eq_singleton_of_realRank_eq_one ds hr
    exact ⟨RealLowRankTemperedData.hasTemperedForm_one d,
      RealLowRankTemperedData.hasScalarCommutant_of_equiv 1 [.character d]
        (RealRankOneStandardModule.evalEquiv d)⟩

/-- Only ranks at least two remain for the global form prerequisite. -/
theorem realTemperedForm_of_rank_ge_two
    (h : ∀ (n : ℕ) (ds : List RealBlock), realRank ds = n →
      (∀ x ∈ ds, ∀ y ∈ ds, realBlockExponent x = realBlockExponent y) →
      2 ≤ n → RealTemperedCommutantReduction.HasTemperedForm n ds) :
    RealTemperedFormStatement := by
  intro n ds hr he
  by_cases hn : n ≤ 1
  · exact (realLowRankTemperedData n ds hr hn).1
  · exact h n ds hr he (by omega)

/-- Only ranks at least two remain for the global scalar-commutant prerequisite. -/
theorem realTemperedScalarCommutant_of_rank_ge_two
    (h : ∀ (n : ℕ) (ds : List RealBlock), realRank ds = n →
      (∀ x ∈ ds, ∀ y ∈ ds, realBlockExponent x = realBlockExponent y) →
      2 ≤ n → RealTemperedCommutantReduction.HasScalarCommutant n ds) :
    RealTemperedScalarCommutantStatement := by
  intro n ds hr he
  by_cases hn : n ≤ 1
  · exact (realLowRankTemperedData n ds hr hn).2
  · exact h n ds hr he (by omega)

end Langlands.Archimedean
