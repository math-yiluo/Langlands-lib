import Langlands.GroupScheme.Torus.PointsTensorGalois
import Langlands.FieldTheory.DimensionLEOneFiniteUnits
import Langlands.Cohomology.Tate.FreeTensorCohomologicalTrivialityProof

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped MonoidalCategory CategoryTheory.MonObj

namespace Langlands.GroupScheme.TorusPointsTensorGalois

set_option backward.isDefEq.respectTransparency false

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  (T : CommGroupScheme (Spec (CommRingCat.of k)))

/-- Actual splitting makes the lifted cocharacter representation free as a module. -/
theorem latticeRepresentation_free (hT : IsSplitTorus (baseChanged k L T).toGrp) :
    Module.Free (ULift.{u} ℤ) (latticeRepresentation k L T) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let c := (TorusPointsTensor.latticeCongr
    (T := baseChanged k L T)
    (T' := splitTorus.commGroupScheme (Spec (CommRingCat.of L)) I) e).trans
      (TorusPointsTensor.latticeCoordinates L I)
  exact Module.Free.of_equiv c.symm

variable [FiniteDimensional k L] [IsGalois k L]

/-- Actual coefficient points have vanishing first cohomology on a splitting cover. -/
theorem pointRepresentation_H1_isZero
    (hk : Langlands.FieldTheory.HasDimensionLEOne k)
    (hT : IsSplitTorus (baseChanged k L T).toGrp) :
    IsZero (groupCohomology
      (GaloisCocycle.pointRepresentation (G := T.toGrp) (k := k) (L := L)) 1) := by
  let : Fintype (L ≃ₐ[k] L) := Fintype.ofFinite _
  let : Module.Free (ULift.{u} ℤ) (latticeRepresentation k L T) :=
    latticeRepresentation_free k L T hT
  let : Module.Flat (ULift.{u} ℤ) (latticeRepresentation k L T) := Module.Flat.of_free
  have hz := Langlands.Tate.FreeTensor.tensor_isZero
    (Langlands.ClassFieldTheory.Local.unitsRepresentation k L)
    (latticeRepresentation k L T) hk.finite_units_cohomologicallyTrivial (1 : ℤ)
  have hp : IsZero (tateCohomology
      (GaloisCocycle.pointRepresentation (G := T.toGrp) (k := k) (L := L)) 1) :=
    hz.of_iso ((tateCohomologyFunctor 1).mapIso (tensorPointIso k L T hT)).symm
  exact hp.of_iso ((TateCohomology.isoGroupCohomology 1).app _).symm

/-- The norm criterion trivializes actual cocycles over a finite Galois splitting cover. -/
theorem cocycle_isTrivial
    (hk : Langlands.FieldTheory.HasDimensionLEOne k)
    (hT : IsSplitTorus (baseChanged k L T).toGrp)
    (ξ : Cocycle T.toGrp (GaloisCocycle.cover k L)) : ξ.IsTrivial :=
  GaloisCocycle.isTrivial_of_H1_isZero ξ (pointRepresentation_H1_isZero k L T hk hT)

/-- A chosen actual trivializing point on the original finite Galois splitting cover. -/
def cocycleTrivializingPoint
    (hk : Langlands.FieldTheory.HasDimensionLEOne k)
    (hT : IsSplitTorus (baseChanged k L T).toGrp)
    (ξ : Cocycle T.toGrp (GaloisCocycle.cover k L)) :
    GaloisCocycle.cover k L ⟶ T.X :=
  Classical.choose (cocycle_isTrivial k L T hk hT ξ)

/-- The chosen point gives the coboundary formula on every relative test scheme. -/
theorem cocycleTrivializingPoint_spec
    (hk : Langlands.FieldTheory.HasDimensionLEOne k)
    (hT : IsSplitTorus (baseChanged k L T).toGrp)
    (ξ : Cocycle T.toGrp (GaloisCocycle.cover k L))
    {Z : Over (Spec (CommRingCat.of k))} (a b : Z ⟶ GaloisCocycle.cover k L) :
    ξ.toFun a b =
      (a ≫ cocycleTrivializingPoint k L T hk hT ξ) *
        (b ≫ cocycleTrivializingPoint k L T hk hT ξ)⁻¹ :=
  Classical.choose_spec (cocycle_isTrivial k L T hk hT ξ) a b

end Langlands.GroupScheme.TorusPointsTensorGalois
