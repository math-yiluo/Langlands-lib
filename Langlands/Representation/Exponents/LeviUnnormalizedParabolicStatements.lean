import Langlands.Representation.Exponents.LeviJacquetCompletionNormalization
import Langlands.Representation.Smooth.FiniteLengthGrothendieck
import Langlands.GroupScheme.Reductive.Basic

/-! # The unnormalized parabolic functors `Ind_P^G` and `j_N` (Renard VI.1.1)

Renard 2026, VI.1.1 (printed pp.134–135 / PDF pp.140–141): for a parabolic `P = MN` of `G`,
the unnormalized Jacquet functor `j_N : M(G) → M(M)`, `(π, V) ↦ (π_N, V_N)`, is left adjoint
to `Ind_P^G : M(M) → M(G)`, the smooth induction of the trivial extension to `P`; both functors
are exact (Theorem); `j_N` preserves colimits and `Ind_P^G` preserves limits (Corollary); and
`Ind_P^G` also preserves colimits (Remark). The functors are those of a represented parabolic,
transported to smooth representations of `M(F)` through the Levi-point identification.
-/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VI.1.1, Theorem, adjunction part: for every actual rational parabolic with rational
Levi and matching geometric unipotent radical, every smooth representation `π` of `G(F)` and
every smooth representation `σ` of `M(F)`, evaluation at the identity of `G(F)` descends through
the unnormalized Jacquet quotient `π_N` and gives a linear bijection
`Hom_G(π, Ind_P^G σ) ≃ Hom_M(π_N, σ)`. Here `Ind_P^G σ` is smooth induction from `P(F)` of the
inflation of `σ` along the Levi projection, with no normalizing character. -/
def LeviUnnormalizedFrobeniusReciprocityStatement : Prop :=
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
      let h := isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul
      ∀ (π : SmoothRep.{0, u, w} ℂ (rationalPoints G))
        (σ : SmoothRep.{0, u, v} ℂ (rationalPoints M)),
        let σP := (inflationFunctor h).obj (SmoothRep.pullback (leviPointsEquiv p l hp hl).symm σ)
        ∃ e : π.representation.IntertwiningMap
              ((Induction.smoothInductionFunctor (pointImage p)).obj σP).representation ≃ₗ[ℂ]
            ((leviUnnormalizedJacquetFunctor p l r hp hr hl).obj π).representation.IntertwiningMap
              σ.representation,
          ∀ (F : π.representation.IntertwiningMap
              ((Induction.smoothInductionFunctor (pointImage p)).obj σP).representation) (x : π),
            e F (Jacquet.Localization.mk π.representation (pointImage (r ≫ p)) 1 x) =
              Induction.eval (pointImage p) σP.ρ (F x) 1

/-- Renard VI.1.1, Theorem, last sentence: the unnormalized functors `Ind_P^G` and `j_N` send
every actual short exact sequence of smooth representations to a short exact sequence. -/
def LeviUnnormalizedFunctorsExactStatement : Prop :=
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
      let h := isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul
      let Ind : SmoothRep.{0, u, v} ℂ (rationalPoints M) ⥤
          SmoothRep.{0, u, max u v} ℂ (rationalPoints G) :=
        SmoothRep.pullbackFunctor (leviPointsEquiv p l hp hl).symm ⋙ inflationFunctor h ⋙
          Induction.smoothInductionFunctor (pointImage p)
      (∀ {A B C : SmoothRep.{0, u, v} ℂ (rationalPoints M)} (f : A ⟶ B) (g : B ⟶ C),
        SmoothRep.IsShortExact (SmoothRep.hom f) (SmoothRep.hom g) →
          SmoothRep.IsShortExact (SmoothRep.hom (Ind.map f)) (SmoothRep.hom (Ind.map g))) ∧
      (∀ {A B C : SmoothRep.{0, u, v} ℂ (rationalPoints G)} (f : A ⟶ B) (g : B ⟶ C),
        SmoothRep.IsShortExact (SmoothRep.hom f) (SmoothRep.hom g) →
          SmoothRep.IsShortExact
            (SmoothRep.hom ((leviUnnormalizedJacquetFunctor p l r hp hr hl).map f))
            (SmoothRep.hom ((leviUnnormalizedJacquetFunctor p l r hp hr hl).map g)))

/-- Renard VI.1.1, Corollary and Remark: the unnormalized `j_N` preserves colimits, and
`Ind_P^G` preserves limits (Corollary) and colimits (Remark), of diagrams indexed by categories
`J : Type v` with morphisms in `Type v`. -/
def LeviUnnormalizedFunctorsPreserveLimitsStatement : Prop :=
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
      let h := isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul
      let Ind : SmoothRep.{0, u, v} ℂ (rationalPoints M) ⥤
          SmoothRep.{0, u, max u v} ℂ (rationalPoints G) :=
        SmoothRep.pullbackFunctor (leviPointsEquiv p l hp hl).symm ⋙ inflationFunctor h ⋙
          Induction.smoothInductionFunctor (pointImage p)
      Limits.PreservesColimitsOfSize.{v, v}
          (leviUnnormalizedJacquetFunctor.{u, v} p l r hp hr hl) ∧
        Limits.PreservesLimitsOfSize.{v, v} Ind ∧ Limits.PreservesColimitsOfSize.{v, v} Ind

/-- Renard VI.1.1: the conjunction of the three statements above. -/
def LeviUnnormalizedParabolicStatements : Prop :=
  LeviUnnormalizedFrobeniusReciprocityStatement.{u, v, w} ∧
    LeviUnnormalizedFunctorsExactStatement.{u, v} ∧
      LeviUnnormalizedFunctorsPreserveLimitsStatement.{u, v}

end Langlands.Aubert.General.RepresentedParabolic
