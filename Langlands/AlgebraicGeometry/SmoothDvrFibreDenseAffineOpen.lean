import Langlands.AlgebraicGeometry.SmoothDvrFibreDenseAffineOpenReduction
import Langlands.AlgebraicGeometry.NormalCodimensionOneAffineNeighbourhood
import Langlands.AlgebraicGeometry.SmoothDvrFibreDenseAffineOpenStatement

/-! # A fibre-dense affine open of a smooth separated scheme over an arbitrary DVR -/

universe u

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace Langlands.AlgebraicGeometry

/-- An actual fibre-dense affine open over an arbitrary DVR.
No geometric premise beyond smoothness, quasi-compactness and separatedness
of the structural morphism is required. -/
def smoothDvrFibreDenseAffineOpen
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of R))
    [Smooth p] [QuasiCompact p] [IsSeparated p] : FibreDenseAffineOpen p := by
  have : Finite (Spec (CommRingCat.of R)) := SmoothDvrFibreGenericPoints.finite_base R
  let U := normalCodimensionOneAffineNeighbourhood p
    (fun x => Smooth.isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing R p x)
    (fibreGenericPoints p) (finite_fibreGenericPoints p)
    (fun x hx => SmoothDvrFibreGenericPoints.ringKrullDim_stalk_le_one R X p x hx)
  exact ⟨U.val, U.property.1, (fibreGenericPoints_subset_iff p _).mp U.property.2⟩

/-- The open and both properties supplied by the actual constructor. -/
theorem exists_smoothDvrFibreDenseAffineOpen
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of R))
    [Smooth p] [QuasiCompact p] [IsSeparated p] :
    ∃ U : X.Opens, IsAffineOpen U ∧
      ∀ x : X, ∃ y : X, y ∈ U ∧ p y = p x ∧ y ⤳ x :=
  ⟨(smoothDvrFibreDenseAffineOpen R X p).val,
    (smoothDvrFibreDenseAffineOpen R X p).property⟩

/-- The unchanged proposition interface follows immediately from the actual data. -/
theorem smoothDvrFibreDenseAffineOpenStatement :
    SmoothDvrFibreDenseAffineOpenStatement.{u} := by
  intro R _ _ _ X p hs hq hsep
  exact exists_smoothDvrFibreDenseAffineOpen R X p

end Langlands.AlgebraicGeometry
