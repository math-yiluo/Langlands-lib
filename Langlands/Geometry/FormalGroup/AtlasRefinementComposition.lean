import Langlands.Geometry.FormalGroup.AtlasRefinementMorphism

/-! # Composition of actual principal-cover refinements -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ : Type} [Finite σ]

attribute [local instance] coefficientAlgebra coefficientScalarTower

namespace CoverRefinement

variable {X : BasicAtlas O R σ}

/-- Every principal chart is a refinement of itself. -/
def refl (X : BasicAtlas O R σ) : CoverRefinement X where
  opens := X.opens
  covers := X.covers
  source := id
  contains b := IsLocalization.Away.algebraMap_isUnit b.val

/-- Compose actual localization containments, choosing the original source chart. -/
def comp (q : CoverRefinement X) (r : CoverRefinement q.atlas) : CoverRefinement X where
  opens := r.opens
  covers := r.covers
  source b := q.source (r.source b)
  contains b := q.source_unit (CommAlgCat.of R (Localization.Away b.val))
    (r.source b) (r.contains b)

variable (q : CoverRefinement X) (r : CoverRefinement q.atlas)

/-- Both coefficient routes from the original chart to the final localization agree. -/
theorem comp_coefficient (b : r.opens) :
    (q.comp r).chartCoefficient b =
      (r.chartCoefficient b).comp (q.chartCoefficient (r.source b)) := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers ((q.comp r).source b).val)
  ext a
  change (q.comp r).chartCoefficient b
      (algebraMap R (Localization.Away (q.source (r.source b)).val) a) =
    r.chartCoefficient b (q.chartCoefficient (r.source b)
      (algebraMap R (Localization.Away (q.source (r.source b)).val) a))
  exact ((q.comp r).chartCoefficient_algebraMap b a).trans
    ((congrArg (r.chartCoefficient b) (q.chartCoefficient_algebraMap (r.source b) a)).trans
      (r.chartCoefficient_algebraMap b a)).symm

/-- Compare direct and successive restriction through the actual original law. -/
def compChartIso (A : CommAlgCat.{v} R) (b : r.opens)
    (hb : IsUnit (algebraMap R A b.val)) :
    ModuleLaw.Iso
      (((q.comp r).chart b).map (coefficientLift (O := O) b.val A hb))
      ((r.chart b).map (coefficientLift (O := O) b.val A hb)) :=
  ((q.comp r).chartIso A b hb).trans
    (((r.chartIso A b hb).trans
      (q.chartIso A (r.source b) (r.source_unit A b hb))).symm)

@[simp]
theorem compChartIso_hom_coordinates (A : CommAlgCat.{v} R) (b : r.opens)
    (hb : IsUnit (algebraMap R A b.val)) :
    (q.compChartIso r A b hb).hom.toHom.toCoordinateMap = CoordinateMap.id := by
  change (CoordinateMap.id.comp CoordinateMap.id).comp CoordinateMap.id = CoordinateMap.id
  simp only [CoordinateMap.id_comp]

@[simp]
theorem compChartIso_inv_coordinates (A : CommAlgCat.{v} R) (b : r.opens)
    (hb : IsUnit (algebraMap R A b.val)) :
    (q.compChartIso r A b hb).inv.toHom.toCoordinateMap = CoordinateMap.id := by
  change CoordinateMap.id.comp (CoordinateMap.id.comp CoordinateMap.id) = CoordinateMap.id
  simp only [CoordinateMap.id_comp]

/-- Successive restriction has the original transition coordinates at the composite sources. -/
theorem successive_transition_coordinates (A : CommAlgCat.{v} R) (b c : r.opens)
    (hb : IsUnit (algebraMap R A b.val)) (hc : IsUnit (algebraMap R A c.val)) :
    (r.transition A b c hb hc).hom.toHom.toCoordinateMap =
      (X.transition A (q.source (r.source b)) (q.source (r.source c))
        ((q.comp r).source_unit A b hb) ((q.comp r).source_unit A c hc)).hom.toHom.toCoordinateMap :=
  (r.transition_coordinates A b c hb hc).trans
    (q.transition_coordinates A (r.source b) (r.source c)
      (r.source_unit A b hb) (r.source_unit A c hc))

/-- The direct and successive formal transition maps have equal coordinates. -/
theorem comp_transition_coordinates (A : CommAlgCat.{v} R) (b c : r.opens)
    (hb : IsUnit (algebraMap R A b.val)) (hc : IsUnit (algebraMap R A c.val)) :
    ((q.comp r).transition A b c hb hc).hom.toHom.toCoordinateMap =
      (r.transition A b c hb hc).hom.toHom.toCoordinateMap :=
  ((q.comp r).transition_coordinates A b c hb hc).trans
    (q.successive_transition_coordinates r A b c hb hc).symm

/-- The identity-coordinate maps from direct to successive restriction form a formal atlas map. -/
def compHom : Hom (q.comp r).atlas r.atlas rfl where
  hom A b hb := (q.compChartIso r A b hb).hom
  natural φ b ha hb := by
    change ((CoordinateMap.id.comp CoordinateMap.id).comp CoordinateMap.id).map
      φ.hom.toRingHom = (CoordinateMap.id.comp CoordinateMap.id).comp CoordinateMap.id
    simp only [CoordinateMap.id_comp, CoordinateMap.map_id]
  transition A b c hb hc := by
    apply ModuleLaw.Hom.ext
    apply CommLaw.Hom.ext
    change (r.transition A b c hb hc).hom.toHom.toCoordinateMap.comp
      ((CoordinateMap.id.comp CoordinateMap.id).comp CoordinateMap.id) =
      ((CoordinateMap.id.comp CoordinateMap.id).comp CoordinateMap.id).comp
        ((q.comp r).transition A b c hb hc).hom.toHom.toCoordinateMap
    simp only [CoordinateMap.id_comp, CoordinateMap.comp_id]
    exact (q.comp_transition_coordinates r A b c hb hc).symm

/-- The reverse identity-coordinate maps also commute with formal transitions. -/
def compInv : Hom r.atlas (q.comp r).atlas rfl where
  hom A b hb := (q.compChartIso r A b hb).inv
  natural φ b ha hb := by
    change (CoordinateMap.id.comp (CoordinateMap.id.comp CoordinateMap.id)).map
      φ.hom.toRingHom = CoordinateMap.id.comp (CoordinateMap.id.comp CoordinateMap.id)
    simp only [CoordinateMap.id_comp, CoordinateMap.map_id]
  transition A b c hb hc := by
    apply ModuleLaw.Hom.ext
    apply CommLaw.Hom.ext
    change ((q.comp r).transition A b c hb hc).hom.toHom.toCoordinateMap.comp
      (CoordinateMap.id.comp (CoordinateMap.id.comp CoordinateMap.id)) =
      (CoordinateMap.id.comp (CoordinateMap.id.comp CoordinateMap.id)).comp
        (r.transition A b c hb hc).hom.toHom.toCoordinateMap
    simp only [CoordinateMap.id_comp, CoordinateMap.comp_id]
    exact q.comp_transition_coordinates r A b c hb hc

/-- Direct and successive restriction are genuinely formally isomorphic on their common cover. -/
def compIso : Iso (q.comp r).atlas r.atlas rfl where
  hom := q.compHom r
  inv := q.compInv r
  inv_hom := by
    apply Hom.ext
    intro A b hb
    exact (q.compChartIso r A b hb).inv_hom
  hom_inv := by
    apply Hom.ext
    intro A b hb
    exact (q.compChartIso r A b hb).hom_inv

/-- The formal comparison identifies direct family restriction with successive restriction. -/
theorem comp_onPoints (A : CommAlgCat.{v} R) (x : X.Point A) :
    (q.compIso r).hom.onPoints A ((q.comp r).onPoints A x) =
      r.onPoints A (q.onPoints A x) := by
  apply Subtype.ext
  funext t
  let z : SeriesPoint t.algebra σ Empty :=
    x.val ⟨t.algebra, t.map, q.source (r.source t.chart),
      (q.comp r).source_unit t.algebra t.chart t.isUnit⟩
  change SeriesPoint.eval (q.compChartIso r t.algebra t.chart t.isUnit).hom.toHom.toCoordinateMap z = z
  exact (congrArg (fun F : CoordinateMap t.algebra σ σ => SeriesPoint.eval F z)
    (q.compChartIso_hom_coordinates r t.algebra t.chart t.isUnit)).trans
      (SeriesPoint.eval_id z)

end CoverRefinement

end Langlands.FormalGroup.ModuleLaw.BasicAtlas
