import Langlands.Representation.Exponents.ArbitraryParabolicTempered

/-! # Subrepresentation closure of normalized-exponent temperedness -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- The subrepresentation step used in Renard VII.2.6: normalized-exponent
temperedness passes through an injective smooth intertwiner. -/
def NormalizedTemperedSubrepresentationStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (π τ : SmoothRep.{0, u, v} ℂ (rationalPoints G))
      (f : π ⟶ τ), Function.Injective (SmoothRep.hom f) →
        IsNormalizedExponentTempered hG τ → IsNormalizedExponentTempered hG π

end Langlands.Aubert.General.RepresentedParabolic
