import Langlands.Geometry.Analytic.BoundedEquivalence.Definitions
import Langlands.Geometry.Analytic.TatePresentation

/-! # Changes of actual affinoid presentation -/

noncomputable section

universe u

namespace Langlands.Analytic

namespace PresentedStrictAffinoidAlgebra

variable (K : Type u) [NormedField K] [IsUltrametricDist K]

/-- Every presented algebra is recovered by taking its actual closed ideal
as the relation set. This does not assume ideals are automatically closed. -/
theorem ofRelations_ideal (P : PresentedStrictAffinoidAlgebra K) :
    ofRelations K P.arity (P.ideal : Set (StrictTateAlgebra (Fin P.arity) K)) = P := by
  cases P with
  | mk n I hI =>
    simp only [ofRelations, Ideal.span_eq, Ideal.closure_eq_of_isClosed I hI]

/-- Equality of presentation objects induces the bounded algebra equivalence
of their actual quotient carriers. -/
def equivOfEq {P Q : PresentedStrictAffinoidAlgebra K} (h : P = Q) :
    BoundedAlgEquiv K P Q := by
  subst Q
  exact BoundedAlgEquiv.refl K P

/-- Select an actual Tate-series representative of a quotient element.
All later constructions record its proved projection equation. -/
def representative (P : PresentedStrictAffinoidAlgebra K) (a : P) :
    StrictTateAlgebra (Fin P.arity) K :=
  (presentationMap_surjective K P a).choose

@[simp]
theorem presentationMap_representative (P : PresentedStrictAffinoidAlgebra K) (a : P) :
    presentationMap K P (representative K P a) = a :=
  (presentationMap_surjective K P a).choose_spec

end PresentedStrictAffinoidAlgebra

end Langlands.Analytic
