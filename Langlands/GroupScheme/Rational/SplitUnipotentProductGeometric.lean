import Langlands.GroupScheme.Rational.SplitUnipotentProductGeometry
import Langlands.GroupScheme.Rational.SubgroupProductGeometry
import Langlands.GroupScheme.GeometricConnectedness

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot.ProductGeometry

def secondFactorInversionIso {S : Scheme.{u}} (V C : GroupScheme S) :
    V.X ⊗ C.X ≅ V.X ⊗ C.X :=
  Iso.refl V.X ⊗ᵢ asIso (GrpObj.inv (X := C.X))

theorem secondFactorInversionIso_hom_comp_orbitMap
    {S : Scheme.{u}} {V C U : GroupScheme S} (j : V ⟶ U) (c : C ⟶ U) :
    (secondFactorInversionIso V C).hom ≫ (SubgroupProductOrbit.action j c).orbitMap 1 =
      subgroupMultiplication j c := by
  rw [SubgroupProductOrbit.comp_orbitMap_one]
  simp [secondFactorInversionIso, subgroupMultiplication, Hom.inv_def]

theorem smooth_surjective_subgroupMultiplication_of_lie_dimension
    {k : Type u} [Field k] [IsAlgClosed k]
    {V C U : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth V.X.hom] [IsAffineHom V.X.hom] [ConnectedSpace V.X.left]
    [Smooth C.X.hom] [IsAffineHom C.X.hom] [ConnectedSpace C.X.left]
    [Smooth U.X.hom] [IsAffineHom U.X.hom] [ConnectedSpace U.X.left]
    (j : V ⟶ U) (c : C ⟶ U) (hc : IsClosedSubgroup c)
    [IsAffineHom (subgroupIntersection j c).X.hom]
    (hV : IsUnipotent V) (hC : IsUnipotent C)
    (hE : Smooth (subgroupIntersection j c).X.hom)
    (hdim : Lie.dimension V + Lie.dimension C =
      Lie.dimension (subgroupIntersection j c) + Lie.dimension U) :
    Smooth (subgroupMultiplication j c).left ∧
      Surjective (subgroupMultiplication j c).left := by
  let : Smooth (V ⊗ C).X.hom :=
    prop_tensor_hom (@Smooth) V.X C.X inferInstance inferInstance
  let : IsAffineHom (V ⊗ C).X.hom :=
    prop_tensor_hom (@IsAffineHom) V.X C.X inferInstance inferInstance
  let : GeometricallyConnected C.X.hom := C.geometricallyConnected_of_connected
  let : ConnectedSpace (V ⊗ C).X.left := by
    change ConnectedSpace ↥(pullback V.X.hom C.X.hom)
    infer_instance
  let : IsAffine C.X.left := isAffine_of_isAffineHom C.X.hom
  let : IsClosedImmersion c.hom.hom.left := hc
  let : IsClosedImmersion (subgroupIntersectionFst j c).hom.hom.left :=
    isClosedSubgroup_subgroupIntersectionFst j hc
  let : IsAffineHom (subgroupIntersection j c).X.hom := by
    rw [← Over.w (subgroupIntersectionFst j c).hom.hom]
    infer_instance
  have hdim' : Lie.dimension (V ⊗ C) =
      Lie.dimension (subgroupIntersection j c) + Lie.dimension U := by
    rw [SubgroupProductOrbit.lie_dimension_tensor]
    exact hdim
  obtain ⟨hs, hsurj⟩ := orbitMap_smooth_surjective_of_dimension
    (SubgroupProductOrbit.action j c) 1 (SubgroupProductOrbit.intersectionDiagonal j c)
    (SubgroupProductOrbit.closed_intersectionDiagonal j c hc) hE
    (SubgroupProductOrbit.orbit_fibers j c)
    (SubgroupProductOrbit.isClosed_range_orbitMap j c hV hC) hdim'
  let := hs
  let := hsurj
  let e := secondFactorInversionIso V C
  have : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  have he := congrArg Over.Hom.left (secondFactorInversionIso_hom_comp_orbitMap j c)
  change e.hom.left ≫ ((SubgroupProductOrbit.action j c).orbitMap 1).left =
    (subgroupMultiplication j c).left at he
  constructor <;> rw [← he] <;> infer_instance

end Langlands.GroupScheme.RelativeRoot.ProductGeometry
