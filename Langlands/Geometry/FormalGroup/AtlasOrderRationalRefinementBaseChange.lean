import Langlands.Geometry.FormalGroup.AtlasOrderRefinementBaseChange
import Langlands.Geometry.FormalGroup.AtlasOrderRationalTransition
import Langlands.Geometry.FormalGroup.AtlasOrderQuasiIsogenyCalculus

/-! # Actual rational chart maps for refinement and coefficient extension -/

noncomputable section

universe u v w z

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas.CoverRefinement

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {σ : Type} [Finite σ] {X : BasicAtlas O R σ}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- Identify an extended refined chart with the source selected before extension. -/
def baseLeftOrderChartIso (q : CoverRefinement X) (E : BasicAtlas.OrderAction D X)
    (S : CommAlgCat.{v} R) (B : CommAlgCat.{v} S) (b : q.atlas.baseOpens S)
    (hb : IsUnit (algebraMap S B b.val)) :
    ModuleLaw.OrderAction.Iso
      ((((q.orderAction E).baseChange S).chart b).map
        (coefficientLift (O := O) b.val B hb))
      ((E.chart (q.baseOriginalSource S b)).map
        (coefficientLift (O := O) (q.baseOriginalSource S b).val (BasicAtlas.restrictTest S B)
          (q.baseOriginal_unit S B b hb))) :=
  ((q.orderAction E).baseOrderChartIso S B b hb).trans
    (q.orderChartIso E (BasicAtlas.restrictTest S B) (q.atlas.baseSource S b)
      (q.atlas.baseSource_unit S B b hb))

/-- Identify a refined extended chart with the source selected after extension. -/
def baseRightOrderChartIso (q : CoverRefinement X) (E : BasicAtlas.OrderAction D X)
    (S : CommAlgCat.{v} R) (B : CommAlgCat.{v} S) (b : q.atlas.baseOpens S)
    (hb : IsUnit (algebraMap S B b.val)) :
    ModuleLaw.OrderAction.Iso
      (((q.baseChange S).orderChart (E.baseChange S) b).map
        (coefficientLift (O := O) b.val B hb))
      ((E.chart (q.baseSelectedSource S b)).map
        (coefficientLift (O := O) (q.baseSelectedSource S b).val (BasicAtlas.restrictTest S B)
          (q.baseSelected_unit S B b hb))) :=
  ((q.baseChange S).orderChartIso (E.baseChange S) B b hb).trans
    (E.baseOrderChartIso S B ((q.baseChange S).source b)
      ((q.baseChange S).source_unit B b hb))

variable {F : Type z} [Field F] [Algebra O F] [IsDomain O] [IsFractionRing O F]

/-- Evaluate the specified refinement/coefficient-extension formal isomorphism rationally. -/
def orderBaseChangeQuasi (q : CoverRefinement X) (E : BasicAtlas.OrderAction D X)
    (S : CommAlgCat.{v} R) (B : CommAlgCat.{v} S) (b : q.atlas.baseOpens S)
    (hb : IsUnit (algebraMap S B b.val)) :
    ModuleLaw.OrderAction.QuasiIsogeny F
      ((((q.orderAction E).baseChange S).chart b).map
        (coefficientLift (O := O) b.val B hb))
      (((q.baseChange S).orderChart (E.baseChange S) b).map
        (coefficientLift (O := O) b.val B hb)) :=
  (BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := F)
    (q.orderBaseChangeIso E S)).onChart B b hb

/-- The evaluated map followed by the selected-source identification is the original-source
identification followed by the actual transition between those two sources. -/
theorem orderBaseChangeQuasi_chart (q : CoverRefinement X)
    (E : BasicAtlas.OrderAction D X) (S : CommAlgCat.{v} R)
    (B : CommAlgCat.{v} S) (b : q.atlas.baseOpens S)
    (hb : IsUnit (algebraMap S B b.val)) :
    (q.orderBaseChangeQuasi (F := F) E S B b hb).trans
        (ModuleLaw.OrderAction.QuasiIsogeny.ofIso (q.baseRightOrderChartIso E S B b hb)) =
      (ModuleLaw.OrderAction.QuasiIsogeny.ofIso (q.baseLeftOrderChartIso E S B b hb)).trans
        (ModuleLaw.OrderAction.QuasiIsogeny.ofIso
          (E.transitionIso (BasicAtlas.restrictTest S B)
            (q.baseOriginalSource S b) (q.baseSelectedSource S b)
            (q.baseOriginal_unit S B b hb) (q.baseSelected_unit S B b hb))) := by
  apply ModuleLaw.OrderAction.QuasiIsogeny.ext
  apply ModuleLaw.OrderAction.RationalHom.ext
  let bc := (q.orderBaseChangeIso E S).hom.val.hom B b hb
  let il := (q.baseLeftOrderChartIso E S B b hb).hom.val
  let ir := (q.baseRightOrderChartIso E S B b hb).hom.val
  let tt := (E.transitionIso (BasicAtlas.restrictTest S B)
    (q.baseOriginalSource S b) (q.baseSelectedSource S b)
    (q.baseOriginal_unit S B b hb) (q.baseSelected_unit S B b hb)).hom.val
  have he : ir.comp bc = tt.comp il := by
    apply ModuleLaw.Hom.ext
    apply CommLaw.Hom.ext
    change (CoordinateMap.id.comp CoordinateMap.id).comp
      (q.baseChangeChartIso S B b hb).hom.toHom.toCoordinateMap =
        (X.transition (BasicAtlas.restrictTest S B)
          (q.baseOriginalSource S b) (q.baseSelectedSource S b)
          (q.baseOriginal_unit S B b hb) (q.baseSelected_unit S B b hb)).hom.toHom.toCoordinateMap.comp
            (CoordinateMap.id.comp CoordinateMap.id)
    simpa only [CoordinateMap.id_comp, CoordinateMap.comp_id] using
      q.baseChangeChartIso_coordinates S B b hb
  exact (ModuleLaw.RationalHom.ofHom_comp (F := F) ir bc).symm.trans
    ((congrArg (ModuleLaw.RationalHom.ofHom (F := F)) he).trans
      (ModuleLaw.RationalHom.ofHom_comp (F := F) tt il))

/-- The actual commuting square retains both selected-source identifications. -/
def orderBaseChangeChartSquare (q : CoverRefinement X)
    (E : BasicAtlas.OrderAction D X) (S : CommAlgCat.{v} R)
    (B : CommAlgCat.{v} S) (b : q.atlas.baseOpens S)
    (hb : IsUnit (algebraMap S B b.val)) :
    ModuleLaw.OrderAction.QuasiIsogeny.CommutingSquare (F := F)
      ((((q.orderAction E).baseChange S).chart b).map
        (coefficientLift (O := O) b.val B hb))
      (((q.baseChange S).orderChart (E.baseChange S) b).map
        (coefficientLift (O := O) b.val B hb))
      ((E.chart (q.baseSelectedSource S b)).map
        (coefficientLift (O := O) (q.baseSelectedSource S b).val (BasicAtlas.restrictTest S B)
          (q.baseSelected_unit S B b hb)))
      ((E.chart (q.baseOriginalSource S b)).map
        (coefficientLift (O := O) (q.baseOriginalSource S b).val (BasicAtlas.restrictTest S B)
          (q.baseOriginal_unit S B b hb))) where
  top := q.orderBaseChangeQuasi E S B b hb
  right := ModuleLaw.OrderAction.QuasiIsogeny.ofIso (q.baseRightOrderChartIso E S B b hb)
  left := ModuleLaw.OrderAction.QuasiIsogeny.ofIso (q.baseLeftOrderChartIso E S B b hb)
  bottom := ModuleLaw.OrderAction.QuasiIsogeny.ofIso
    (E.transitionIso (BasicAtlas.restrictTest S B)
      (q.baseOriginalSource S b) (q.baseSelectedSource S b)
      (q.baseOriginal_unit S B b hb) (q.baseSelected_unit S B b hb))
  commutes := q.orderBaseChangeQuasi_chart E S B b hb

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.CoverRefinement
