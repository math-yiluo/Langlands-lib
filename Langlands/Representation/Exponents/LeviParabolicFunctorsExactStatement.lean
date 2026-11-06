import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints
import Langlands.Representation.Smooth.FiniteLengthGrothendieck
import Langlands.GroupScheme.Reductive.Basic

/-! # Exactness of normalized parabolic induction and restriction

Renard 2026, VI.1.2 Proposition (printed p.136/PDF p.142), exactness part: for a
parabolic `P = MN` of `G`, the functors `i_P^G : M(M) → M(G)` and
`r_P^G : M(G) → M(M)` are exact. Both functors are the published normalized functors of
a represented parabolic, transported to smooth representations of `M(F)` through the
Levi-point identification. Exactness is stated as preservation of actual short exact
sequences.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VI.1.2 Proposition, exactness part: for every actual rational parabolic with
rational Levi and matching geometric unipotent radical, normalized parabolic induction
`i_P^G` and normalized Jacquet restriction `r_P^G` send every actual short exact
sequence of smooth representations to a short exact sequence. -/
def LeviParabolicFunctorsExactStatement : Prop :=
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
      (∀ {A B C : SmoothRep.{0, u, v} ℂ (rationalPoints M)} (f : A ⟶ B) (g : B ⟶ C),
        SmoothRep.IsShortExact (SmoothRep.hom f) (SmoothRep.hom g) →
          SmoothRep.IsShortExact
            (SmoothRep.hom ((leviInductionFunctor p l r hp hr hl hmul).map f))
            (SmoothRep.hom ((leviInductionFunctor p l r hp hr hl hmul).map g))) ∧
      (∀ {A B C : SmoothRep.{0, u, v} ℂ (rationalPoints G)} (f : A ⟶ B) (g : B ⟶ C),
        SmoothRep.IsShortExact (SmoothRep.hom f) (SmoothRep.hom g) →
          SmoothRep.IsShortExact
            (SmoothRep.hom ((leviJacquetFunctor p l r hp hr hl hmul).map f))
            (SmoothRep.hom ((leviJacquetFunctor p l r hp hr hl hmul).map g)))

end Langlands.Aubert.General.RepresentedParabolic
