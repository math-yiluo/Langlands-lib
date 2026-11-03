import Langlands.Representation.Aubert.General.GeometricK0Target
import Langlands.Representation.Aubert.General.LeviInductionNormalization
import Langlands.Representation.Aubert.General.LeviJacquetNormalization

/-! # Ambient normalization of the actual geometric target induction -/

noncomputable section

open CategoryTheory

namespace Langlands.Aubert.General

universe uI uG uV

section Normalizer

variable {G : Type uG} [Group G] {ι : Type uI}
variable (P M U : Finset ι → Subgroup G)

/-- The supplied actual target decomposition already forces normalization of
the entire ambient target radical by the actual target parabolic. -/
theorem geometricTargetParabolic_normalizes (I J : Finset ι) (n : G)
    (ht : GeometricTargetDecomposition P M U I J n) :
    geometricTargetIntersection (M I) (P J) n ≤
      Subgroup.normalizer (geometricTargetIntersection (M I) (U J) n : Set G) :=
  normalizes_of_subgroupOf inf_le_left inf_le_left ht.le_normalizer

end Normalizer

section Terms

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] {ι : Type uI}
variable (P M U : Finset ι → Subgroup G)
variable (hM : ∀ I, IsClosed (M I : Set G)) (hU : ∀ I, IsClosed (U I : Set G))

/-- The actual target induction, displayed using the ambient positive
half-modulus on its full intersection parabolic, after actual Levi inflation.
Its ambient normalizer witness is derived from `ht`. -/
def geometricTargetAmbientInductionFunctor (I J : Finset ι) (n : G)
    (ht : GeometricTargetDecomposition P M U I J n) :
    SmoothRep.{0, uG, uV} ℂ (geometricTargetIntersection (M I) (M J) n) ⥤
      SmoothRep.{0, uG, max uG uV} ℂ (M I) :=
  ambientLeviInductionFunctor (hM I) inf_le_left ht
    (isClosed_geometricTargetIntersection (M I) (U J) (hM I) (hU J) n)
    inf_le_left (geometricTargetParabolic_normalizes P M U I J n ht)

/-- Equality with the published actual target functor, with no additional
ambient normalization or character-compatibility premise. -/
theorem geometricTargetInductionFunctor_eq_ambient (I J : Finset ι) (n : G)
    (ht : GeometricTargetDecomposition P M U I J n) :
    geometricTargetInductionFunctor.{uI, uG, uV} P M U hM hU I J n ht =
      geometricTargetAmbientInductionFunctor P M U hM hU I J n ht :=
  leviNormalizedInductionFunctor_eq_ambient (hM I) inf_le_left ht
    (isClosed_geometricTargetIntersection (M I) (U J) (hM I) (hU J) n)
    inf_le_left inf_le_left (geometricTargetParabolic_normalizes P M U I J n ht)

/-- Natural normalization comparison at the literal target intersection
parabolic, Levi, and radical of the geometric term. -/
def geometricTargetInductionNormalizationIso (I J : Finset ι) (n : G)
    (ht : GeometricTargetDecomposition P M U I J n) :
    geometricTargetInductionFunctor.{uI, uG, uV} P M U hM hU I J n ht ≅
      geometricTargetAmbientInductionFunctor P M U hM hU I J n ht :=
  eqToIso (geometricTargetInductionFunctor_eq_ambient P M U hM hU I J n ht)

/-- The actual source Jacquet and conjugation functors followed by the
ambient-normalized target realization. -/
def geometricTermTargetAmbientFunctor (I J : Finset ι) (n : G)
    (hs : GeometricSourceDecomposition P M U I J n)
    (ht : GeometricTargetDecomposition P M U I J n) :
    SmoothRep.{0, uG, max uG uV} ℂ (M J) ⥤
      SmoothRep.{0, uG, max uG uV} ℂ (M I) :=
  geometricSourceJacquetFunctor P M U hM hU I J n hs ⋙
    conjugationFunctor n (geometricIntersectionMembership (M I) (M J) n) ⋙
      geometricTargetAmbientInductionFunctor P M U hM hU I J n ht

/-- Replacing only the target endpoint preserves the actual composite. -/
theorem geometricTermFunctor_eq_targetAmbient (I J : Finset ι) (n : G)
    (hs : GeometricSourceDecomposition P M U I J n)
    (ht : GeometricTargetDecomposition P M U I J n) :
    geometricTermFunctor.{uI, uG, uV} P M U hM hU I J n hs ht =
      geometricTermTargetAmbientFunctor P M U hM hU I J n hs ht := by
  unfold geometricTermFunctor geometricTermTargetAmbientFunctor
  rw [geometricTargetInductionFunctor_eq_ambient P M U hM hU I J n ht]

/-- Finite length is inherited from the existing actual term and its four
named preservation hypotheses. -/
theorem geometricTermTargetAmbient_hasFiniteLength (I J : Finset ι) (n : G)
    (hs : GeometricSourceDecomposition P M U I J n)
    (ht : GeometricTargetDecomposition P M U I J n)
    (hfl : GeometricTermFiniteLength.{uI, uG, uV} P M U hM hU I J n hs ht)
    (A : SmoothRep.{0, uG, max uG uV} ℂ (M J)) (hA : A.HasFiniteLength) :
    ((geometricTermTargetAmbientFunctor P M U hM hU I J n hs ht).obj A).HasFiniteLength := by
  rw [← geometricTermFunctor_eq_targetAmbient P M U hM hU I J n hs ht]
  exact geometricTerm_hasFiniteLength P M U hM hU I J n hs ht hfl A hA

set_option maxHeartbeats 800000 in
/-- The exact actual term map sends an actual representation class to this
ambient-normalized target realization, with finite length derived above. -/
theorem geometricTermK0_ofRepresentation_targetAmbient (I J : Finset ι) (n : G)
    (hs : GeometricSourceDecomposition P M U I J n)
    (ht : GeometricTargetDecomposition P M U I J n)
    (hfl : GeometricTermFiniteLength.{uI, uG, uV} P M U hM hU I J n hs ht)
    (A : SmoothRep.{0, uG, max uG uV} ℂ (M J)) (hA : A.HasFiniteLength) :
    geometricTermK0.{uI, uG, uV} P M U hM hU I J n hs ht hfl
        (SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation A hA) =
      SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation
        ((geometricTermTargetAmbientFunctor P M U hM hU I J n hs ht).obj A)
        (geometricTermTargetAmbient_hasFiniteLength P M U hM hU I J n hs ht hfl A hA) := by
  simpa only [geometricTermFunctor_eq_targetAmbient P M U hM hU I J n hs ht] using
    geometricTermK0_ofRepresentation P M U hM hU I J n hs ht hfl A hA

end Terms

end Langlands.Aubert.General
