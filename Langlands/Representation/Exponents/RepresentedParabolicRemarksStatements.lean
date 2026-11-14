import Langlands.Representation.Exponents.LeviUnnormalizedParabolicStatements
import Langlands.Representation.Exponents.LeviSupercuspidalInductionSupport
import Langlands.GroupScheme.Rational.StandardParabolic
import Langlands.GroupScheme.Rational.SplitTorus

/-! # Two remarks on represented parabolics: Renard VI.1.1 and VI.2.1

Renard 2026, VI.1.1 Remark, first sentence (printed p.135 / PDF p.141): the unnormalized
parabolic induction `Ind_P^G : M(M) → M(G)` has a right adjoint. Renard VI.2.1, first block of
Remarks, Remark 1 (printed p.137 / PDF p.143): a smooth representation is supercuspidal as soon
as its Jacquet modules along the proper *standard* parabolics vanish. Both are stated for the
actual rational parabolics of the represented interface.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VI.1.1, Remark, first sentence: for every actual rational parabolic `P = MN` (with
rational Levi `M` and matching geometric unipotent radical `N`), the unnormalized parabolic
induction `Ind_P^G : M(M) → M(G)` (inflation along `P → M` followed by smooth induction from
`P(F)`, with no normalizing character) has a right adjoint. Both categories have carriers in
the common universe `max u v`, where `u` is the universe of the field. -/
def LeviUnnormalizedInductionRightAdjointStatement : Prop :=
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
      let Ind : SmoothRep.{0, u, max u v} ℂ (rationalPoints M) ⥤
          SmoothRep.{0, u, max u v} ℂ (rationalPoints G) :=
        SmoothRep.pullbackFunctor (leviPointsEquiv p l hp hl).symm ⋙ inflationFunctor h ⋙
          Induction.smoothInductionFunctor (pointImage p)
      Ind.IsLeftAdjoint

/-- Renard VI.2.1, first block of Remarks, Remark 1: fix a maximal split torus `i : T → G` and a
generic cocharacter `ν`, which determine the minimal parabolic and the simple relative roots
`Δ`. A smooth representation `A` of `G(F)` is supercuspidal (its normalized Jacquet module
vanishes along every proper actual rational parabolic) if and only if it vanishes along every
proper *standard* one: every actual rational parabolic `p` with rational Levi `l` and geometric
unipotent radical `r` whose subgroup functors are the standard parabolic `P_J` and the standard
Levi `M_J` of some `J ⊆ Δ`. -/
def SupercuspidalStandardParabolicCriterionStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G),
      IsMaximalSplitTorus i →
      ∀ (ν : cocharacterLattice T), IsGenericCocharacter i ν →
      ∀ (A : SmoothRep.{0, u, v} ℂ (rationalPoints G)),
        IsSupercuspidal A ↔
          ∀ (P M U : GroupScheme (Spec (CommRingCat.of k)))
            (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
            (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
            (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
            (hmul : IsIso (subgroupMultiplication l r)) (J : Set (characterLattice T)),
            J ⊆ simpleRelativeRoots i ν →
            SubgroupFunctor.range p = standardParabolic i ν J →
            SubgroupFunctor.range (l ≫ p) = standardLevi i ν J →
            ¬ IsIso p → Subsingleton ((jacquetFunctor p l r hp hr hl hmul).obj A)

end Langlands.Aubert.General.RepresentedParabolic
