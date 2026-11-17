import Langlands.AlgebraicGeometry.SmoothDvrFibreGenericPoints
import Langlands.AlgebraicGeometry.NormalCodimensionOneAffineNeighbourhoodStatement

/-! # Affine-open data from the normal common-neighbourhood theorem -/

universe u

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace Langlands.AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- An actual affine open containing a same-fibre generization of every point. -/
def FibreDenseAffineOpen (p : X ⟶ S) :=
  {U : X.Opens // IsAffineOpen U ∧ FibreGenerizationDense p (U : Set X)}

namespace FibreDenseAffineOpen

def opens {p : X ⟶ S} (U : FibreDenseAffineOpen p) : X.Opens := U.val

theorem isAffineOpen {p : X ⟶ S} (U : FibreDenseAffineOpen p) :
    IsAffineOpen U.opens := U.property.1

theorem exists_generization {p : X ⟶ S} (U : FibreDenseAffineOpen p) (x : X) :
    ∃ y : X, y ∈ U.opens ∧ p y = p x ∧ y ⤳ x := U.property.2 x

end FibreDenseAffineOpen

/-- The common-neighbourhood theorem gives the actual DVR affine-open data.
The argument `h` is the general geometric theorem, whose proof is separate. -/
def smoothDvrFibreDenseAffineOpenOfNormalNeighbourhoods
    (h : NormalCodimensionOneAffineNeighbourhoodStatement.{u})
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of R))
    [Smooth p] [QuasiCompact p] [IsSeparated p] : FibreDenseAffineOpen p := by
  have : Finite (Spec (CommRingCat.of R)) := SmoothDvrFibreGenericPoints.finite_base R
  have hex : ∃ U : X.Opens, IsAffineOpen U ∧ fibreGenericPoints p ⊆ U :=
    h R X p inferInstance inferInstance inferInstance
      (fun x => Smooth.isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing R p x)
      (fibreGenericPoints p) (finite_fibreGenericPoints p)
      (fun x hx => SmoothDvrFibreGenericPoints.ringKrullDim_stalk_le_one R X p x hx)
  exact ⟨Classical.choose hex, (Classical.choose_spec hex).1,
    (fibreGenericPoints_subset_iff p _).mp (Classical.choose_spec hex).2⟩

end Langlands.AlgebraicGeometry
