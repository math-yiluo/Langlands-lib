import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints
import Langlands.GroupScheme.Reductive.Basic

/-! # Limits and colimits under normalized parabolic induction and restriction

Renard 2026, VI.1.2 Corollary (printed p.136/PDF p.142): for a parabolic `P = MN` of
`G`, normalized parabolic induction `i_P^G` preserves limits and colimits, and normalized
parabolic restriction `r_P^G` preserves colimits. Both functors are the published
normalized functors of a represented parabolic, transported to smooth representations of
`M(F)`. Limits and colimits are indexed by categories in `Type v`, the morphism universe
of the source categories.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VI.1.2 Corollary: for every actual rational parabolic with rational Levi and
matching geometric unipotent radical, `i_P^G` preserves limits and colimits, and `r_P^G`
preserves colimits, of diagrams indexed by categories `J : Type v` with morphisms in
`Type v`. -/
def LeviParabolicFunctorsPreserveLimitsStatement : Prop :=
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
      Limits.PreservesLimitsOfSize.{v, v} (leviInductionFunctor.{u, v} p l r hp hr hl hmul) ∧
        Limits.PreservesColimitsOfSize.{v, v} (leviInductionFunctor.{u, v} p l r hp hr hl hmul) ∧
        Limits.PreservesColimitsOfSize.{v, v} (leviJacquetFunctor.{u, v} p l r hp hr hl hmul)

end Langlands.Aubert.General.RepresentedParabolic
