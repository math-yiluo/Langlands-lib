import Langlands.Representation.Exponents.ArbitraryParabolicTempered
import Langlands.Representation.Category.Basic

/-! # Central characters of nonzero normalized-exponent tempered representations

This is a corrected derived normalized-parameter formulation of the second
assertion in Renard VII.2.1, Remark 1. The paired Markdown explains the necessary
nonzero qualification and the separate normalization and proof obligations.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- A prescribed scalar character on the full point-group center of a nonzero
normalized-exponent tempered representation is unitary at every point. -/
def NormalizedTemperedCentralCharacterStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)]
      [NonarchimedeanGroup (rationalPoints G)]
      (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)) [Nontrivial π]
      (ω : Subgroup.center (rationalPoints G) →* ℂˣ),
      IsNormalizedExponentTempered hG π →
      π.HasCentralCharacter ω →
        ∀ z : Subgroup.center (rationalPoints G), ‖(ω z : ℂ)‖ = 1

end Langlands.Aubert.General.RepresentedParabolic
