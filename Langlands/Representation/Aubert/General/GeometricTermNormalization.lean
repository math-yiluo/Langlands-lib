import Langlands.Representation.Aubert.General.GeometricSourceNormalization
import Langlands.Representation.Aubert.General.GeometricTargetNormalization

/-! # Ambient normalization of both endpoints of the actual geometric term -/

noncomputable section

open CategoryTheory

namespace Langlands.Aubert.General

universe uI uG uV

open SmoothRep

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] {ι : Type uI}
variable (P M U : Finset ι → Subgroup G)
variable (hM : ∀ I, IsClosed (M I : Set G)) (hU : ∀ I, IsClosed (U I : Set G))

/-- The actual geometric term with both endpoint half-characters evaluated
using their respective actual radicals in the ambient group. -/
def geometricTermAmbientFunctor (I J : Finset ι) (n : G)
    (hs : GeometricSourceDecomposition P M U I J n)
    (ht : GeometricTargetDecomposition P M U I J n) :
    SmoothRep.{0, uG, max uG uV} ℂ (M J) ⥤
      SmoothRep.{0, uG, max uG uV} ℂ (M I) :=
  geometricSourceAmbientJacquetFunctor P M U hM hU I J n hs ⋙
    conjugationFunctor n (geometricIntersectionMembership (M I) (M J) n) ⋙
      geometricTargetAmbientInductionFunctor P M U hM hU I J n ht

/-- The published target equality also applies after exposing the ambient
source inverse half-character. -/
theorem geometricTermSourceAmbientFunctor_eq_ambient (I J : Finset ι) (n : G)
    (hs : GeometricSourceDecomposition P M U I J n)
    (ht : GeometricTargetDecomposition P M U I J n) :
    geometricTermSourceAmbientFunctor.{uI, uG, uV} P M U hM hU I J n hs ht =
      geometricTermAmbientFunctor P M U hM hU I J n hs ht := by
  unfold geometricTermSourceAmbientFunctor geometricTermAmbientFunctor
  rw [geometricTargetInductionFunctor_eq_ambient P M U hM hU I J n ht]

/-- Combine the actual source natural isomorphism with the actual target
equality, retaining the original conjugation functor. -/
def geometricTermAmbientIso (I J : Finset ι) (n : G)
    (hs : GeometricSourceDecomposition P M U I J n)
    (ht : GeometricTargetDecomposition P M U I J n) :
    geometricTermFunctor.{uI, uG, uV} P M U hM hU I J n hs ht ≅
      geometricTermAmbientFunctor P M U hM hU I J n hs ht :=
  geometricTermSourceAmbientIso P M U hM hU I J n hs ht ≪≫
    eqToIso (geometricTermSourceAmbientFunctor_eq_ambient P M U hM hU I J n hs ht)

set_option maxHeartbeats 800000 in
/-- The existing four actual term-preservation hypotheses give finite length
of the presentation with both ambient endpoint characters. -/
theorem geometricTermAmbient_hasFiniteLength (I J : Finset ι) (n : G)
    (hs : GeometricSourceDecomposition P M U I J n)
    (ht : GeometricTargetDecomposition P M U I J n)
    (hfl : GeometricTermFiniteLength.{uI, uG, uV} P M U hM hU I J n hs ht)
    (A : SmoothRep.{0, uG, max uG uV} ℂ (M J)) (hA : A.HasFiniteLength) :
    ((geometricTermAmbientFunctor.{uI, uG, uV}
      P M U hM hU I J n hs ht).obj A).HasFiniteLength :=
  hasFiniteLength_of_iso ((geometricTermAmbientIso P M U hM hU I J n hs ht).app A)
    (geometricTerm_hasFiniteLength P M U hM hU I J n hs ht hfl A hA)

set_option maxHeartbeats 800000 in
/-- The existing actual integer-linear K0 term evaluates to the class of the
actual composite with both ambient endpoint characters exposed. -/
theorem geometricTermK0_ofAmbient (I J : Finset ι) (n : G)
    (hs : GeometricSourceDecomposition P M U I J n)
    (ht : GeometricTargetDecomposition P M U I J n)
    (hfl : GeometricTermFiniteLength.{uI, uG, uV} P M U hM hU I J n hs ht)
    (A : SmoothRep.{0, uG, max uG uV} ℂ (M J)) (hA : A.HasFiniteLength) :
    geometricTermK0.{uI, uG, uV} P M U hM hU I J n hs ht hfl
        (FiniteLengthGrothendieckGroup.ofRepresentation A hA) =
      FiniteLengthGrothendieckGroup.ofRepresentation
        ((geometricTermAmbientFunctor.{uI, uG, uV}
          P M U hM hU I J n hs ht).obj A)
        (geometricTermAmbient_hasFiniteLength P M U hM hU I J n hs ht hfl A hA) := by
  rw [geometricTermK0_ofRepresentation]
  exact FiniteLengthGrothendieckGroup.ofObject_eq_of_iso
    ((geometricTermAmbientIso P M U hM hU I J n hs ht).app A)

end Langlands.Aubert.General
