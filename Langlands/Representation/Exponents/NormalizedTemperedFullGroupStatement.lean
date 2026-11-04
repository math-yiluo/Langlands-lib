import Langlands.Representation.Exponents.ArbitraryParabolicTempered

/-! # Full-group exponents of normalized-exponent tempered representations

This is the derived normalized-parameter formulation of the first assertion
in Renard VII.2.1, Remark 1. The paired Markdown retains the separate
source-normalization comparison and full-center consequence.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Every actual normalized Jacquet exponent for the identity parabolic and
identity Levi of a normalized-exponent tempered representation has zero
normalized real part and is unitary on its specified split component. -/
def NormalizedTemperedFullGroupExponentStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)]
      [NonarchimedeanGroup (rationalPoints G)]
      (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
      (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ G)
      (hp : IsParabolicSubgroup (𝟙 G)) (hl : IsRationalLeviSubgroup (𝟙 G))
      (ha : IsSplitComponent a)
      (U : GroupScheme (Spec (CommRingCat.of k))) (r : U ⟶ G)
      (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
      (hmul : IsIso (subgroupMultiplication (𝟙 G) r))
      (χ : rationalPoints A.toGrp →* ℂˣ),
      IsNormalizedExponentTempered hG π →
      IsNormalizedJacquetExponent (𝟙 G) (𝟙 G) r hp hl hr hmul ha π χ →
        Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ = 0 ∧
          ∀ x : rationalPoints A.toGrp, ‖(χ x : ℂ)‖ = 1

end Langlands.Aubert.General.RepresentedParabolic
