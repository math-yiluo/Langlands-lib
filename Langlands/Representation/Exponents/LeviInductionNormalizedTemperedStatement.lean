import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints
import Langlands.Representation.Exponents.ArbitraryParabolicTempered
import Langlands.GroupScheme.Reductive.Basic

/-! # Parabolic induction preserves normalized-exponent temperedness

Renard 2026, VII.2.2 (printed pp.227–228/PDF pp.233–234): for a parabolic `P = MN` of
`G` and a tempered representation `σ` of `M`, the normalized induced representation
`i_P^G σ` is tempered. Temperedness is the published normalized-exponent predicate,
applied to `M(F)` through the Levi-point identification.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VII.2.2: for every actual rational parabolic with rational Levi and matching
geometric unipotent radical, normalized parabolic induction takes representations of
the Levi points that are normalized-exponent tempered to normalized-exponent tempered
representations of `G(F)`. -/
def LeviInductionNormalizedTemperedStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P M U : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
      (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
      (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
      (hmul : IsIso (subgroupMultiplication l r)),
      haveI := hl.isConnectedReductive.isAffineHom
      letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
      haveI : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
      haveI : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
      ∀ σ : SmoothRep.{0, u, v} ℂ (rationalPoints M),
        IsNormalizedExponentTempered hl.isConnectedReductive σ →
          IsNormalizedExponentTempered hG ((leviInductionFunctor p l r hp hr hl hmul).obj σ)

end Langlands.Aubert.General.RepresentedParabolic
