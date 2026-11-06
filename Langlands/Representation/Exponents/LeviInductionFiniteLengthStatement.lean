import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints
import Langlands.Representation.Smooth.FiniteLengthGrothendieckFunctor
import Langlands.GroupScheme.Reductive.Basic

/-! # Normalized parabolic induction preserves finite length

Renard 2026, VI.6.2 (printed p.178/PDF p.184): the functor `i_P^G` preserves representations
of finite length. The Lemma of VI.6.2 is the case of an irreducible representation of `M`;
the general case follows by exactness, as the opening sentence of VI.6.2 announces.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VI.6.2: for every actual rational parabolic `P = MN`, the normalized induction
`i_P^G` sends smooth representations of `M(F)` of finite length to smooth representations of
`G(F)` of finite length. -/
def LeviInductionFiniteLengthStatement : Prop :=
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
      SmoothRep.PreservesFiniteLength (leviInductionFunctor.{u, v} p l r hp hr hl hmul)

end Langlands.Aubert.General.RepresentedParabolic
