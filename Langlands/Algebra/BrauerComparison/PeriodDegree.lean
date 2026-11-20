import Langlands.Algebra.BrauerComparison.AbsoluteComparison
import Mathlib.GroupTheory.OrderOfElement

/-! # The Brauer period divides the reduced degree -/

noncomputable section

universe u v

namespace Langlands.BrauerComparison

open Matrix CentralSimple CentralSimple.SemilinearGaloisAction
open ScalarTwoCocycle (IsTwoCocycle coboundary)

attribute [local instance] coefficientGLAction

section Determinant

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
variable {I : Type v} [Fintype I] [DecidableEq I]

/-- The determinant one-cochain of the chosen invertible lifts of matrix descent. -/
def determinantCochain (ρ : SemilinearGaloisAction K L (Matrix I I L)) :
    Gal(L/K) → Lˣ := fun s => GeneralLinearGroup.det (ρ.innerMatrix s)

private theorem det_coefficientAction (s : Gal(L/K)) (X : GL I L) :
    GeneralLinearGroup.det (s • X) = s • GeneralLinearGroup.det X := by
  apply Units.ext
  exact (s.map_det (X : Matrix I I L)).symm

/-- The size-th power of the scalar defect is the coboundary of the determinants. -/
theorem scalarDefect_pow_card (ρ : SemilinearGaloisAction K L (Matrix I I L))
    (s t : Gal(L/K)) :
    ρ.scalarDefect s t ^ Fintype.card I = coboundary (determinantCochain ρ) s t := by
  have h := congrArg GeneralLinearGroup.det (scalarDefect_formula ρ s t)
  simpa only [GeneralLinearGroup.det_scalar, map_mul, map_inv, det_coefficientAction,
    determinantCochain, coboundary] using h

/-- The size of the matrices annihilates their descent class in relative cohomology. -/
theorem card_nsmul_descentClass [Nonempty I]
    (ρ : SemilinearGaloisAction K L (Matrix I I L)) :
    Fintype.card I • descentClass ρ = 0 := by
  let c : Gal(L/K) → Gal(L/K) → Lˣ := fun s t => ρ.scalarDefect s t ^ Fintype.card I
  have hc : IsTwoCocycle c := by
    intro s t r
    simpa only [c, mul_pow, smul_pow'] using
      congrArg (fun a : Lˣ => a ^ Fintype.card I) (ρ.scalarDefect_isTwoCocycle s t r)
  have hzero : unitClass c hc = 0 :=
    (unitClass_eq_zero_iff c hc).2 ⟨determinantCochain ρ, scalarDefect_pow_card ρ⟩
  have hcochains : Fintype.card I • unitCocycle ρ.scalarDefect ρ.scalarDefect_isTwoCocycle =
      unitCocycle c hc := by
    apply Subtype.ext
    funext st
    rfl
  rw [descentClass, unitClass, ← map_nsmul, hcochains]
  exact hzero

end Determinant

end Langlands.BrauerComparison

namespace Langlands.Brauer

open CentralSimple BrauerComparison ClassFieldTheory.Local

/-- The additive order of the actual Brauer class divides the reduced degree. -/
theorem addOrderOf_classOf_dvd_reducedDegree {K : Type u} [Field K] (A : CSA.{u, u} K) :
    addOrderOf (classOf A) ∣ reducedDegree K A := by
  apply addOrderOf_dvd_iff_nsmul_eq_zero.mpr
  let S := SeparableClosure K
  let F := separableSplittingStage K S A
  let e := separableSplittingChart K S A
  have : Nonempty (Fin (reducedDegree K A)) := Fin.pos_iff_nonempty.mp (reducedDegree_pos K A)
  have hz : reducedDegree K A • relativeClass e = 0 := by
    simpa only [relativeClass, Fintype.card_fin] using
      card_nsmul_descentClass (splittingChartIndexAction e)
  apply (brauerContinuousEquiv K S).injective
  rw [map_zero, map_nsmul, brauerContinuousEquiv_classOf, csaContinuousClass_at_stage K S A F e,
    ← map_nsmul, hz, map_zero]

end Langlands.Brauer
