import Langlands.Geometry.FormalGroup.AtlasOrderCoordinateIso
import Langlands.Geometry.FormalGroup.AtlasOrderRationalTransition
import Langlands.Geometry.FormalGroup.SpecialAtlas

/-! # Coefficient triangles for special formal atlas charts -/

noncomputable section

universe u v s

namespace Langlands.FormalGroup.LocalDivision.SpecialAtlas

open ValuativeRel CentralDivision CategoryTheory ModuleLaw

attribute [local instance] ModuleLaw.coefficientAlgebra ModuleLaw.coefficientScalarTower

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {R : Type v} [CommRing R] [Algebra 𝒪[K] R]
variable (X : SpecialAtlas K D ι R) {A A' : CommAlgCat.{v} R} (f : A ⟶ A')

local notation "θ" => AlgHom.restrictScalars 𝒪[K] (CommAlgCat.Hom.hom f)
local notation "lift[" b ", " S ", " h "]" =>
  BasicAtlas.coefficientLift (O := 𝒪[K]) (Subtype.val b) S h

set_option backward.isDefEq.respectTransparency false in
/-- Extending a test chart and taking the chart on the extended algebra have the same formal series. -/
def chartTestCoefficientIso (b : X.atlas.opens)
    (hb : IsUnit (algebraMap R A b.val)) (hb' : IsUnit (algebraMap R A' b.val)) :
    SpecialModule.Iso ((X.chartTestModule A b hb).mapSameUniverse θ) (X.chartTestModule A' b hb') := by
  have h := BasicAtlas.coefficientLift_comp (O := 𝒪[K]) b.val f hb hb'
  refine ModuleLaw.OrderAction.Iso.ofIdenticalCoordinates ?_ ?_
  · change (((X.atlas.chart b).groupLaw.addition.map (lift[b, A, hb]).toRingHom).map (θ).toRingHom) =
      (X.atlas.chart b).groupLaw.addition.map (lift[b, A', hb']).toRingHom
    rw [CoordinateMap.map_ringHom_comp]
    exact congrArg (fun c : Localization.Away b.val →ₐ[𝒪[K]] A' =>
      (X.atlas.chart b).groupLaw.addition.map c.toRingHom) h
  · intro a
    let q := ((X.order.chart b).action a).toHom.toCoordinateMap
    change ((q.map (lift[b, A, hb]).toRingHom).map (θ).toRingHom) = q.map (lift[b, A', hb']).toRingHom
    rw [CoordinateMap.map_ringHom_comp]
    exact congrArg (fun c : Localization.Away b.val →ₐ[𝒪[K]] A' => q.map c.toRingHom) h

/-- The formal change of chart in the coefficient triangle is the identity on coordinates. -/
@[simp]
theorem chartTestCoefficientIso_coordinateMap (b : X.atlas.opens)
    (hb : IsUnit (algebraMap R A b.val)) (hb' : IsUnit (algebraMap R A' b.val)) :
    (X.chartTestCoefficientIso f b hb hb').hom.val.toHom.toCoordinateMap = CoordinateMap.id :=
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- Coefficient triangles intertwine the actual full-order transitions. -/
theorem chartTestCoefficientIso_transition (b c : X.atlas.opens)
    (hb : IsUnit (algebraMap R A b.val)) (hc : IsUnit (algebraMap R A c.val))
    (hb' : IsUnit (algebraMap R A' b.val)) (hc' : IsUnit (algebraMap R A' c.val)) :
    SpecialModule.Iso.trans
        (X := (X.chartTestModule A b hb).mapSameUniverse θ)
        (Y := (X.chartTestModule A c hc).mapSameUniverse θ) (Z := X.chartTestModule A' c hc')
        (SpecialModule.Iso.mapSameUniverse
          (X := X.chartTestModule A b hb) (Y := X.chartTestModule A c hc)
          (X.order.transitionIso A b c hb hc) θ)
        (X.chartTestCoefficientIso f c hc hc') =
      SpecialModule.Iso.trans (X := (X.chartTestModule A b hb).mapSameUniverse θ)
        (Y := X.chartTestModule A' b hb') (Z := X.chartTestModule A' c hc')
        (X.chartTestCoefficientIso f b hb hb')
        (X.order.transitionIso A' b c hb' hc') := by
  apply ModuleLaw.OrderAction.Iso.ext_hom
  apply Subtype.ext
  apply ModuleLaw.Hom.ext
  apply CommLaw.Hom.ext
  change CoordinateMap.id.comp ((X.atlas.transition A b c hb hc).hom.toHom.toCoordinateMap.map
    f.hom.toRingHom) = (X.atlas.transition A' b c hb' hc').hom.toHom.toCoordinateMap.comp CoordinateMap.id
  rw [CoordinateMap.id_comp, CoordinateMap.comp_id]
  exact X.atlas.transition_natural f b c hb hc hb' hc'

end Langlands.FormalGroup.LocalDivision.SpecialAtlas
