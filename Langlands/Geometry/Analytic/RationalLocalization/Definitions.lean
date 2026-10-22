import Langlands.Geometry.Analytic.BoundedEquivalence
import Langlands.Geometry.Analytic.RationalPresentation.Definitions

/-! # Actual rational quotients of arbitrary presented affinoid algebras -/

noncomputable section

universe u

namespace Langlands.Analytic.RationalLocalization

open StrictTateAlgebra PresentedStrictAffinoidAlgebra

variable (K : Type u) [NormedField K] [IsUltrametricDist K]
  (P : PresentedStrictAffinoidAlgebra K)

/-- The relation model supplied by the presentation's own actual closed ideal. -/
abbrev model : PresentedStrictAffinoidAlgebra K :=
  ofRelations K P.arity (P.ideal : Set (StrictTateAlgebra (Fin P.arity) K))

/-- The relation model is the original presentation, with a bounded equivalence
of the actual quotient carriers. -/
def modelEquiv : BoundedAlgEquiv K (model K P) P :=
  equivOfEq K (ofRelations_ideal K P)

/-- Choose an actual Tate series representing an element in the relation model. -/
def seriesLift (a : P) : StrictTateAlgebra (Fin P.arity) K :=
  representative K (model K P) ((modelEquiv K P).symm a)

@[simp]
theorem presentationMap_seriesLift (a : P) :
    presentationMap K (model K P) (seriesLift K P a) = (modelEquiv K P).symm a :=
  presentationMap_representative K (model K P) _

@[simp]
theorem modelEquiv_presentationMap_seriesLift (a : P) :
    modelEquiv K P (presentationMap K (model K P) (seriesLift K P a)) = a := by
  rw [presentationMap_seriesLift, BoundedAlgEquiv.apply_symm_apply]

variable [CompleteSpace K] (m : ℕ) (g : P) (f : Fin m → P)

/-- The actual rational quotient of `P` by the equations `g * Y_j = f_j`.
Its carrier is constructed from the actual Tate quotient using proved lifts. -/
def algebra : PresentedStrictAffinoidAlgebra K :=
  RationalPresentation.algebra K P.arity m P.ideal
    (seriesLift K P g) (fun j => seriesLift K P (f j))

/-- The bounded map from the original affinoid algebra to its rational quotient. -/
def baseMap : BoundedAlgHom K P (algebra K P m g f) :=
  (RationalPresentation.baseMap K P.arity m P.ideal
    (seriesLift K P g) (fun j => seriesLift K P (f j))).comp
      (modelEquiv K P).symm.toBoundedAlgHom

/-- The new coordinates in the actual rational quotient. -/
def fractionCoordinate (j : Fin m) : algebra K P m g f :=
  coordinate K (algebra K P m g f) (Fin.natAdd P.arity j)

/-- The unit-ideal condition is stated in the original algebra `P`. -/
def GeneratesUnitIdeal : Prop := Ideal.span (insert g (Set.range f)) = ⊤


/-- The rational locus is expressed using the input algebra elements themselves. -/
def locus : Set (BanachSpectrum P) := {x | ∀ j, x (f j) ≤ x g}


end Langlands.Analytic.RationalLocalization
