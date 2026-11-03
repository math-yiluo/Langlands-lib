import Langlands.Representation.Aubert.General.GeometricK0Target
import Langlands.Representation.Aubert.General.LeviJacquetNormalization
import Langlands.Representation.Smooth.FiniteLengthGrothendieckIso

/-! # Ambient normalization of the actual geometric source term -/

noncomputable section

open CategoryTheory

namespace Langlands.Aubert.General

universe uI uG uV

open SmoothRep

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable {ι : Type uI}
variable (P M U : Finset ι → Subgroup G)
variable (hM : ∀ I, IsClosed (M I : Set G)) (hU : ∀ I, IsClosed (U I : Set G))

omit [TopologicalSpace G] [LocallyCompactSpace G] [NonarchimedeanGroup G] in
/-- The actual source intersection Levi normalizes the actual ambient source
radical. Both subgroup containments follow from their literal intersections. -/
theorem geometricSourceLevi_le_normalizer (I J : Finset ι) (n : G)
    (hs : GeometricSourceDecomposition P M U I J n) :
    geometricSourceIntersection (M I) (M J) n ≤
      Subgroup.normalizer (geometricSourceIntersection (U I) (M J) n : Set G) :=
  normalizes_of_subgroupOf inf_le_left inf_le_left hs.levi_le_normalizer

/-- Actual source localization and output subgroup transport, followed by the
inverse half-character of the actual source radical in the ambient group. -/
def geometricSourceAmbientJacquetFunctor (I J : Finset ι) (n : G)
    (hs : GeometricSourceDecomposition P M U I J n) :
    SmoothRep.{0, uG, uV} ℂ (M J) ⥤
      SmoothRep.{0, uG, uV} ℂ (geometricSourceIntersection (M I) (M J) n) :=
  leviAmbientNormalizedJacquetFunctor inf_le_left inf_le_left hs.levi_le_normalizer
    (isClosed_geometricSourceIntersection (U I) (M J) (hU I) (hM J) n)

/-- The actual source Jacquet functor admits the ambient-character presentation,
without an additional normalizer or character-compatibility hypothesis. -/
def geometricSourceJacquetAmbientIso (I J : Finset ι) (n : G)
    (hs : GeometricSourceDecomposition P M U I J n) :
    geometricSourceJacquetFunctor.{uI, uG, uV} P M U hM hU I J n hs ≅
      geometricSourceAmbientJacquetFunctor P M U hM hU I J n hs :=
  leviNormalizedJacquetAmbientIso (hM J) inf_le_left inf_le_left hs
    (isClosed_geometricSourceIntersection (U I) (M J) (hU I) (hM J) n)

/-- The inside inverse half-character of the actual source radical equals its
actual ambient inverse half-character on every element of the source Levi. -/
theorem geometricSourceInverseHalfCharacter_eq
    (I J : Finset ι) (n : G)
    (hs : GeometricSourceDecomposition P M U I J n)
    (l : geometricSourceIntersection (M I) (M J) n) :
    letI : LocallyCompactSpace (M J) := (hM J).locallyCompactSpace
    HaarModulus.closedInverseHalfCharacter
        ((geometricSourceIntersection (U I) (M J) n).subgroupOf (M J))
        ((isClosed_geometricSourceIntersection (U I) (M J) (hU I) (hM J) n).preimage
          continuous_subtype_val)
        ((geometricSourceIntersection (M I) (M J) n).subgroupOf (M J))
        hs.levi_le_normalizer
        ((subgroupOfContinuousEquiv inf_le_left).symm l) =
      HaarModulus.closedInverseHalfCharacter
        (geometricSourceIntersection (U I) (M J) n)
        (isClosed_geometricSourceIntersection (U I) (M J) (hU I) (hM J) n)
        (geometricSourceIntersection (M I) (M J) n)
        (geometricSourceLevi_le_normalizer P M U I J n hs) l :=
  leviInverseHalfCharacter_eq (hM J) inf_le_left inf_le_left hs.levi_le_normalizer
    (isClosed_geometricSourceIntersection (U I) (M J) (hU I) (hM J) n) l

/-- Replace only the source normalization of the actual geometric term.
The forward conjugation and actual target normalized induction are retained. -/
def geometricTermSourceAmbientFunctor (I J : Finset ι) (n : G)
    (hs : GeometricSourceDecomposition P M U I J n)
    (ht : GeometricTargetDecomposition P M U I J n) :
    SmoothRep.{0, uG, max uG uV} ℂ (M J) ⥤
      SmoothRep.{0, uG, max uG uV} ℂ (M I) :=
  geometricSourceAmbientJacquetFunctor P M U hM hU I J n hs ⋙
    conjugationFunctor n (geometricIntersectionMembership (M I) (M J) n) ⋙
      geometricTargetInductionFunctor P M U hM hU I J n ht

/-- The source-normalized presentation is naturally isomorphic to the
published actual geometric term. -/
def geometricTermSourceAmbientIso (I J : Finset ι) (n : G)
    (hs : GeometricSourceDecomposition P M U I J n)
    (ht : GeometricTargetDecomposition P M U I J n) :
    geometricTermFunctor.{uI, uG, uV} P M U hM hU I J n hs ht ≅
      geometricTermSourceAmbientFunctor P M U hM hU I J n hs ht :=
  Functor.isoWhiskerRight
    (geometricSourceJacquetAmbientIso P M U hM hU I J n hs) _

set_option maxHeartbeats 800000 in
/-- The displayed finite-length prerequisites suffice for the actual term
with its source normalization exposed in the ambient group. -/
theorem geometricTermSourceAmbient_hasFiniteLength (I J : Finset ι) (n : G)
    (hs : GeometricSourceDecomposition P M U I J n)
    (ht : GeometricTargetDecomposition P M U I J n)
    (hfl : GeometricTermFiniteLength.{uI, uG, uV} P M U hM hU I J n hs ht)
    (A : SmoothRep.{0, uG, max uG uV} ℂ (M J)) (hA : A.HasFiniteLength) :
    ((geometricTermSourceAmbientFunctor.{uI, uG, uV}
      P M U hM hU I J n hs ht).obj A).HasFiniteLength :=
  hasFiniteLength_of_iso ((geometricTermSourceAmbientIso P M U hM hU I J n hs ht).app A)
    (geometricTerm_hasFiniteLength P M U hM hU I J n hs ht hfl A hA)

set_option maxHeartbeats 800000 in
/-- The published exact-K0 term evaluates to the class of the actual geometric
term with its ambient source inverse half-character exposed. -/
theorem geometricTermK0_ofSourceAmbient (I J : Finset ι) (n : G)
    (hs : GeometricSourceDecomposition P M U I J n)
    (ht : GeometricTargetDecomposition P M U I J n)
    (hfl : GeometricTermFiniteLength.{uI, uG, uV} P M U hM hU I J n hs ht)
    (A : SmoothRep.{0, uG, max uG uV} ℂ (M J)) (hA : A.HasFiniteLength) :
    geometricTermK0.{uI, uG, uV} P M U hM hU I J n hs ht hfl
        (FiniteLengthGrothendieckGroup.ofRepresentation A hA) =
      FiniteLengthGrothendieckGroup.ofRepresentation
        ((geometricTermSourceAmbientFunctor.{uI, uG, uV}
          P M U hM hU I J n hs ht).obj A)
        (geometricTermSourceAmbient_hasFiniteLength
          P M U hM hU I J n hs ht hfl A hA) := by
  rw [geometricTermK0_ofRepresentation]
  exact FiniteLengthGrothendieckGroup.ofObject_eq_of_iso
    ((geometricTermSourceAmbientIso P M U hM hU I J n hs ht).app A)

end Langlands.Aubert.General
