import Langlands.Algebra.NonUnitalModuleAdmissibilityStatements
import Langlands.Algebra.NonUnitalModuleFixedBidualProof
import Langlands.Algebra.NonUnitalModuleBidualInjectionProof

/-! Corrected canonical reflexivity proof in Renard I.5.1. -/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra.NonUnitalModuleAdmissibilityReflexivityProof

open NonUnitalModuleDual NonUnitalModuleAdmissible
open NonUnitalModuleFixedBidualMaps NonUnitalModuleAdmissibilityStatements
open NonUnitalModuleCorner (FixedPart)

universe uA uM

variable {A : Type uA} [NonUnitalRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  {M : Type uM} [AddCommGroup M] [NonUnitalModule A M]
  (hA : IsIdempotented A) (hM : IsNondegenerate A M)

/-- Admissibility is equivalent to bijectivity of the actual canonical evaluation. -/
theorem admissibleIffEvaluationBijective : AdmissibleIffEvaluationBijective hA hM := by
  let _ := dualAction hA hM
  let _ := bidualAction hA hM
  have hi := NonUnitalModuleBidualInjectionProof.evaluation_injective hA hM
  obtain ⟨hinv, hsq⟩ :=
    NonUnitalModuleFixedBidualProof.fixedBidualComparisons A M hA hM
  constructor
  · intro h
    refine ⟨hi, ?_⟩
    intro Φ
    obtain ⟨e, he⟩ := bidual_isNondegenerate hA hM Φ
    let _ := NonUnitalModuleCorner.complexModule hA hM e
    let _ := NonUnitalModuleCorner.complexModule hA (bidual_isNondegenerate hA hM) e
    let _ := h e
    obtain ⟨x, hx⟩ := (Module.bijective_dual_eval ℂ (FixedPart e M)).2
      (toOrdinaryBidual hA hM e ⟨Φ, he⟩)
    refine ⟨x.val, ?_⟩
    calc
      evaluation hA hM x.val =
          (fromOrdinaryBidual hA hM e (Module.Dual.eval ℂ (FixedPart e M) x)).val :=
        (hsq e x).symm
      _ = Φ := by
        have hfix : fromOrdinaryBidual hA hM e
            (Module.Dual.eval ℂ (FixedPart e M) x) = ⟨Φ, he⟩ := by
          rw [hx]
          exact (hinv e).1 ⟨Φ, he⟩
        exact congrArg (fun Ξ : FixedBidual hA hM e => Ξ.val) hfix
  · intro h e
    let _ := NonUnitalModuleCorner.complexModule hA hM e
    let _ := NonUnitalModuleCorner.complexModule hA (bidual_isNondegenerate hA hM) e
    have hsurj : Function.Surjective (Module.Dual.eval ℂ (FixedPart e M)) := by
      intro Ψ
      obtain ⟨m, hm⟩ := h.2 (fromOrdinaryBidual hA hM e Ψ).val
      have he : (e : A) • m = m := by
        apply hi
        rw [evaluation_map_smul, hm]
        exact (fromOrdinaryBidual hA hM e Ψ).property
      let x : FixedPart e M := ⟨m, he⟩
      refine ⟨x, ?_⟩
      apply (hinv e).2.injective
      apply Subtype.ext
      exact (hsq e x).trans hm
    let _ : Module.IsReflexive ℂ (FixedPart e M) :=
      ⟨Module.eval_apply_injective ℂ, hsurj⟩
    infer_instance

end Langlands.Algebra.NonUnitalModuleAdmissibilityReflexivityProof
