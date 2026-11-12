import Langlands.Representation.Exponents.LeviParabolicModulus
import Langlands.Representation.Exponents.ArbitraryParabolicQuotientCompactProof
import Langlands.Representation.Aubert.General.InductionLimits
import Langlands.Representation.Aubert.General.CompactQuotientNaturalDuality
import Langlands.Representation.Aubert.General.ContragredientJacquetTransport
import Langlands.Representation.Aubert.General.CuspidalRemainderTransport
import Langlands.Representation.Aubert.General.RationalReductiveUnimodularityProof
import Langlands.GroupScheme.Rational.StandardCocharacterProof

/-!
# First adjointness and induction duality on represented Levi points

The unconditional inputs to the Hom chain of Renard 2026, VI.9.6, for the actual
normalized functors of a represented parabolic.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G P M N : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance leviDualityPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

/-- Frobenius reciprocity as an adjunction on the actual Levi points. -/
def leviFirstAdjointnessAdjunction
    (p : P ⟶ G) (m : M ⟶ P) (n : N ⟶ P)
    (hp : IsParabolicSubgroup p) (hm : IsRationalLeviSubgroup m)
    (hn : LeviSubgroup.IsGeometricUnipotentRadical n)
    (hmul : IsIso (subgroupMultiplication m n)) :
    let := leviPointTopology m hm
    leviJacquetFunctor.{u, max u v} p m n hp hn hm hmul ⊣
      leviInductionFunctor.{u, max u v} p m n hp hn hm hmul := by
  let := leviPointTopology m hm
  exact (firstAdjointnessAdjunction
    (isSemidirectDecomposition_pointImage p m n hp.isClosedSubgroup hn hmul)
    (isClosed_pointImage_comp p n hp.isClosedSubgroup hn.1.isClosedSubgroup)
    (isUnimodularModulus_pointImage_radical p n hp.isClosedSubgroup hn.1)).comp
      (SmoothRep.pullbackEquivalence (leviPointsEquiv p m hp hm)).toAdjunction

/-- Normalized induction from an actual represented Levi commutes naturally with the
smooth contragredient on every smooth representation. -/
theorem nonempty_leviInductionContragredientIso (hG : IsConnectedReductive G)
    (p : P ⟶ G) (m : M ⟶ P) (n : N ⟶ P)
    (hp : IsParabolicSubgroup p) (hm : IsRationalLeviSubgroup m)
    (hn : LeviSubgroup.IsGeometricUnipotentRadical n)
    (hmul : IsIso (subgroupMultiplication m n)) :
    let := leviPointTopology m hm
    haveI : LocallyCompactSpace (rationalPoints M) :=
      leviPoints_locallyCompactSpace p m hp hm
    haveI : NonarchimedeanGroup (rationalPoints M) :=
      leviPoints_nonarchimedeanGroup p m hp hm
    Nonempty ((leviInductionFunctor.{u, max u v} p m n hp hn hm hmul).op ⋙
        SmoothRep.contragredientFunctor.{0, u, max u v} ≅
      SmoothRep.contragredientFunctor.{0, u, max u v} ⋙
        leviInductionFunctor.{u, max u v} p m n hp hn hm hmul) := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : T2Space (rationalPoints G) := rationalPoint_t2Space k G
  let : MeasurableSpace (rationalPoints G) := borel _
  have : BorelSpace (rationalPoints G) := ⟨rfl⟩
  have : LocallyCompactSpace (pointImage p) :=
    (isClosed_pointImage p hp.isClosedSubgroup).locallyCompactSpace
  have : CompactSpace (Induction.LeftQuotient (pointImage p)) :=
    arbitraryParabolicQuotientCompact k G hG P p hp
  let := leviPointTopology m hm
  have : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p m hp hm
  have : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p m hp hm
  obtain ⟨meas, C, _⟩ := exists_isNaturalIntegralDuality_of_compactSpace.{u, max u v}
    (isSemidirectDecomposition_pointImage p m n hp.isClosedSubgroup hn hmul)
    (isClosed_pointImage_comp p n hp.isClosedSubgroup hn.1.isClosedSubgroup)
    (isClosed_pointImage p hp.isClosedSubgroup)
    (continuous_projection_pointImage p m n hp hm hn hmul)
    (rationalPoints_modularCharacter_eq_one RationalPointFamily.rationalReductiveUnimodularity
      standardCocharacter hG)
    (modularCharacter_pointImage_of_unimodularity
      RationalPointFamily.rationalReductiveUnimodularity standardCocharacter hG
      p m n hp hm hn hmul)
  dsimp only [leviInductionFunctor]
  exact ⟨Functor.associator
      (SmoothRep.pullbackFunctor (leviPointsEquiv p m hp hm).symm).op
      (inductionFunctor.{u, max u v} p m n hp hn hm hmul).op
      SmoothRep.contragredientFunctor.{0, u, max u v} ≪≫
    Functor.isoWhiskerLeft (SmoothRep.pullbackFunctor (leviPointsEquiv p m hp hm).symm).op C ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (contragredientPullbackNatIso (leviPointsEquiv p m hp hm).symm)
      (inductionFunctor p m n hp hn hm hmul) ≪≫
    Functor.associator _ _ _⟩

end Langlands.Aubert.General.RepresentedParabolic
