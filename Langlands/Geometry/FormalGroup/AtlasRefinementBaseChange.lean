import Langlands.Geometry.FormalGroup.AtlasBaseChangeMorphism
import Langlands.Geometry.FormalGroup.AtlasRefinementSource

/-! # Coefficient extension of actual principal-cover refinements -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ : Type} [Finite σ]
variable {X : BasicAtlas O R σ}

attribute [local instance] coefficientAlgebra coefficientScalarTower

namespace CoverRefinement

variable (q : CoverRefinement X) (S : CommAlgCat.{v} R)

/-- The image of the original source chart for a chosen finer generator. -/
def baseImageSource (b : q.atlas.baseOpens S) : (X.baseChange S).opens :=
  ⟨algebraMap R S (q.source (q.atlas.baseSource S b)).val,
    ⟨(q.source (q.atlas.baseSource S b)).val,
      (q.source (q.atlas.baseSource S b)).property, rfl⟩⟩

/-- Localization containment persists even if coefficient extension merges generators. -/
theorem baseImageSource_unit (b : q.atlas.baseOpens S) :
    IsUnit (algebraMap S (Localization.Away b.val) (q.baseImageSource S b).val) := by
  let A : CommAlgCat.{v} S := CommAlgCat.of S (Localization.Away b.val)
  have h := q.source_unit (BasicAtlas.restrictTest S A) (q.atlas.baseSource S b)
    (q.atlas.baseSource_unit S A b (IsLocalization.Away.algebraMap_isUnit b.val))
  exact h

/-- Extend the finer cover and its actual localization containments. -/
def baseChange : CoverRefinement (X.baseChange S) where
  opens := q.atlas.baseOpens S
  covers := q.atlas.baseOpens_covers S
  source := q.baseImageSource S
  contains := q.baseImageSource_unit S

/-- The original source selected before extending the finer atlas. -/
abbrev baseOriginalSource (b : q.atlas.baseOpens S) : X.opens :=
  q.source (q.atlas.baseSource S b)

/-- The original source selected after refining the extended atlas. -/
abbrev baseSelectedSource (b : q.atlas.baseOpens S) : X.opens :=
  X.baseSource S ((q.baseChange S).source b)

theorem baseOriginal_unit (A : CommAlgCat.{v} S) (b : q.atlas.baseOpens S)
    (hb : IsUnit (algebraMap S A b.val)) :
    IsUnit (algebraMap R (BasicAtlas.restrictTest S A) (q.baseOriginalSource S b).val) :=
  q.source_unit (BasicAtlas.restrictTest S A) (q.atlas.baseSource S b)
    (q.atlas.baseSource_unit S A b hb)

theorem baseSelected_unit (A : CommAlgCat.{v} S) (b : q.atlas.baseOpens S)
    (hb : IsUnit (algebraMap S A b.val)) :
    IsUnit (algebraMap R (BasicAtlas.restrictTest S A) (q.baseSelectedSource S b).val) :=
  X.baseSource_unit S A ((q.baseChange S).source b) ((q.baseChange S).source_unit A b hb)

/-- Compare the extended finer chart with its original law on a restricted test. -/
def baseLeftChartIso (A : CommAlgCat.{v} S) (b : q.atlas.baseOpens S)
    (hb : IsUnit (algebraMap S A b.val)) :
    ModuleLaw.Iso
      (((q.atlas.baseChange S).chart b).map (coefficientLift (O := O) b.val A hb))
      ((X.chart (q.baseOriginalSource S b)).map
        (coefficientLift (O := O) (q.baseOriginalSource S b).val (BasicAtlas.restrictTest S A)
          (q.baseOriginal_unit S A b hb))) :=
  (q.atlas.baseChartIso S A b hb).trans
    (q.chartIso (BasicAtlas.restrictTest S A) (q.atlas.baseSource S b)
      (q.atlas.baseSource_unit S A b hb))

/-- Compare the refined extended chart with its selected original law. -/
def baseRightChartIso (A : CommAlgCat.{v} S) (b : q.atlas.baseOpens S)
    (hb : IsUnit (algebraMap S A b.val)) :
    ModuleLaw.Iso
      ((((q.baseChange S).atlas).chart b).map (coefficientLift (O := O) b.val A hb))
      ((X.chart (q.baseSelectedSource S b)).map
        (coefficientLift (O := O) (q.baseSelectedSource S b).val (BasicAtlas.restrictTest S A)
          (q.baseSelected_unit S A b hb))) :=
  ((q.baseChange S).chartIso A b hb).trans
    (X.baseChartIso S A ((q.baseChange S).source b) ((q.baseChange S).source_unit A b hb))

/-- Refinement and coefficient extension compare through an actual original transition. -/
def baseChangeChartIso (A : CommAlgCat.{v} S) (b : q.atlas.baseOpens S)
    (hb : IsUnit (algebraMap S A b.val)) :
    ModuleLaw.Iso
      (((q.atlas.baseChange S).chart b).map (coefficientLift (O := O) b.val A hb))
      ((((q.baseChange S).atlas).chart b).map (coefficientLift (O := O) b.val A hb)) :=
  (q.baseLeftChartIso S A b hb).trans
    ((X.transition (BasicAtlas.restrictTest S A) (q.baseOriginalSource S b) (q.baseSelectedSource S b)
      (q.baseOriginal_unit S A b hb) (q.baseSelected_unit S A b hb)).trans
        (q.baseRightChartIso S A b hb).symm)

/-- The forward chart comparison has the original transition's full formal series. -/
theorem baseChangeChartIso_coordinates (A : CommAlgCat.{v} S) (b : q.atlas.baseOpens S)
    (hb : IsUnit (algebraMap S A b.val)) :
    (q.baseChangeChartIso S A b hb).hom.toHom.toCoordinateMap =
      (X.transition (BasicAtlas.restrictTest S A) (q.baseOriginalSource S b) (q.baseSelectedSource S b)
        (q.baseOriginal_unit S A b hb) (q.baseSelected_unit S A b hb)).hom.toHom.toCoordinateMap := by
  change ((CoordinateMap.id.comp CoordinateMap.id).comp
    (X.transition (BasicAtlas.restrictTest S A) (q.baseOriginalSource S b) (q.baseSelectedSource S b)
      (q.baseOriginal_unit S A b hb) (q.baseSelected_unit S A b hb)).hom.toHom.toCoordinateMap).comp
        (CoordinateMap.id.comp CoordinateMap.id) = _
  simp only [CoordinateMap.id_comp, CoordinateMap.comp_id]

/-- The extended finer atlas has original transition series at the first selected sources. -/
theorem baseLeftTransition_coordinates (A : CommAlgCat.{v} S) (b c : q.atlas.baseOpens S)
    (hb : IsUnit (algebraMap S A b.val)) (hc : IsUnit (algebraMap S A c.val)) :
    ((q.atlas.baseChange S).transition A b c hb hc).hom.toHom.toCoordinateMap =
      (X.transition (BasicAtlas.restrictTest S A) (q.baseOriginalSource S b) (q.baseOriginalSource S c)
        (q.baseOriginal_unit S A b hb) (q.baseOriginal_unit S A c hc)).hom.toHom.toCoordinateMap :=
  (q.atlas.baseTransition_coordinates S A b c hb hc).trans
    (q.transition_coordinates (BasicAtlas.restrictTest S A) (q.atlas.baseSource S b)
      (q.atlas.baseSource S c) (q.atlas.baseSource_unit S A b hb)
        (q.atlas.baseSource_unit S A c hc))

/-- The refined extended atlas has original transitions at the second selected sources. -/
theorem baseRightTransition_coordinates (A : CommAlgCat.{v} S) (b c : q.atlas.baseOpens S)
    (hb : IsUnit (algebraMap S A b.val)) (hc : IsUnit (algebraMap S A c.val)) :
    ((q.baseChange S).atlas.transition A b c hb hc).hom.toHom.toCoordinateMap =
      (X.transition (BasicAtlas.restrictTest S A) (q.baseSelectedSource S b) (q.baseSelectedSource S c)
        (q.baseSelected_unit S A b hb) (q.baseSelected_unit S A c hc)).hom.toHom.toCoordinateMap :=
  ((q.baseChange S).transition_coordinates A b c hb hc).trans
    (X.baseTransition_coordinates S A ((q.baseChange S).source b) ((q.baseChange S).source c)
      ((q.baseChange S).source_unit A b hb) ((q.baseChange S).source_unit A c hc))

/-- Refinement and coefficient extension commute by an actual formal atlas map. -/
def baseChangeHom : Hom (q.atlas.baseChange S) (q.baseChange S).atlas rfl where
  hom A b hb := (q.baseChangeChartIso S A b hb).hom
  natural φ b ha hb := by
    change ((q.baseChangeChartIso S _ b ha).hom.toHom.toCoordinateMap).map
      φ.hom.toRingHom = (q.baseChangeChartIso S _ b hb).hom.toHom.toCoordinateMap
    exact (congrArg (fun F : CoordinateMap _ σ σ => F.map φ.hom.toRingHom)
      (q.baseChangeChartIso_coordinates S _ b ha)).trans
      ((X.transition_natural (restrictTestHom S φ) _ _ _ _ _ _).trans
        (q.baseChangeChartIso_coordinates S _ b hb).symm)
  transition A b c hb hc := by
    apply ModuleLaw.Hom.ext
    apply CommLaw.Hom.ext
    change ((q.baseChange S).atlas.transition A b c hb hc).hom.toHom.toCoordinateMap.comp
      (q.baseChangeChartIso S A b hb).hom.toHom.toCoordinateMap =
      (q.baseChangeChartIso S A c hc).hom.toHom.toCoordinateMap.comp
        ((q.atlas.baseChange S).transition A b c hb hc).hom.toHom.toCoordinateMap
    exact (congrArg₂ (fun F G : CoordinateMap A σ σ => F.comp G)
      (q.baseRightTransition_coordinates S A b c hb hc)
      (q.baseChangeChartIso_coordinates S A b hb)).trans
      (((congrArg (fun f => f.hom.toHom.toCoordinateMap)
      (X.transition_cocycle (BasicAtlas.restrictTest S A)
        (q.baseOriginalSource S b) (q.baseSelectedSource S b) (q.baseSelectedSource S c)
        (q.baseOriginal_unit S A b hb) (q.baseSelected_unit S A b hb)
        (q.baseSelected_unit S A c hc))).trans
      (congrArg (fun f => f.hom.toHom.toCoordinateMap)
        (X.transition_cocycle (BasicAtlas.restrictTest S A)
          (q.baseOriginalSource S b) (q.baseOriginalSource S c) (q.baseSelectedSource S c)
          (q.baseOriginal_unit S A b hb) (q.baseOriginal_unit S A c hc)
          (q.baseSelected_unit S A c hc))).symm).trans
        (congrArg₂ (fun F G : CoordinateMap A σ σ => F.comp G)
          (q.baseChangeChartIso_coordinates S A c hc)
          (q.baseLeftTransition_coordinates S A b c hb hc)).symm)

/-- Reverse the comparison using the original transition in the opposite direction. -/
def baseChangeInvChartIso (A : CommAlgCat.{v} S) (b : q.atlas.baseOpens S)
    (hb : IsUnit (algebraMap S A b.val)) :
    ModuleLaw.Iso
      ((((q.baseChange S).atlas).chart b).map (coefficientLift (O := O) b.val A hb))
      (((q.atlas.baseChange S).chart b).map (coefficientLift (O := O) b.val A hb)) :=
  (q.baseRightChartIso S A b hb).trans
    ((X.transition (BasicAtlas.restrictTest S A) (q.baseSelectedSource S b) (q.baseOriginalSource S b)
      (q.baseSelected_unit S A b hb) (q.baseOriginal_unit S A b hb)).trans
        (q.baseLeftChartIso S A b hb).symm)

/-- The reverse chart map retains the full reverse original transition series. -/
theorem baseChangeInvChartIso_coordinates (A : CommAlgCat.{v} S) (b : q.atlas.baseOpens S)
    (hb : IsUnit (algebraMap S A b.val)) :
    (q.baseChangeInvChartIso S A b hb).hom.toHom.toCoordinateMap =
      (X.transition (BasicAtlas.restrictTest S A) (q.baseSelectedSource S b) (q.baseOriginalSource S b)
        (q.baseSelected_unit S A b hb) (q.baseOriginal_unit S A b hb)).hom.toHom.toCoordinateMap := by
  change ((CoordinateMap.id.comp CoordinateMap.id).comp
    (X.transition (BasicAtlas.restrictTest S A) (q.baseSelectedSource S b) (q.baseOriginalSource S b)
      (q.baseSelected_unit S A b hb) (q.baseOriginal_unit S A b hb)).hom.toHom.toCoordinateMap).comp
        (CoordinateMap.id.comp CoordinateMap.id) = _
  simp only [CoordinateMap.id_comp, CoordinateMap.comp_id]

/-- The reverse actual formal atlas map is natural and compatible with transitions. -/
def baseChangeInv : Hom (q.baseChange S).atlas (q.atlas.baseChange S) rfl where
  hom A b hb := (q.baseChangeInvChartIso S A b hb).hom
  natural φ b ha hb := by
    change ((q.baseChangeInvChartIso S _ b ha).hom.toHom.toCoordinateMap).map
      φ.hom.toRingHom = (q.baseChangeInvChartIso S _ b hb).hom.toHom.toCoordinateMap
    exact (congrArg (fun F : CoordinateMap _ σ σ => F.map φ.hom.toRingHom)
      (q.baseChangeInvChartIso_coordinates S _ b ha)).trans
      ((X.transition_natural (restrictTestHom S φ) _ _ _ _ _ _).trans
        (q.baseChangeInvChartIso_coordinates S _ b hb).symm)
  transition A b c hb hc := by
    apply ModuleLaw.Hom.ext
    apply CommLaw.Hom.ext
    change ((q.atlas.baseChange S).transition A b c hb hc).hom.toHom.toCoordinateMap.comp
      (q.baseChangeInvChartIso S A b hb).hom.toHom.toCoordinateMap =
      (q.baseChangeInvChartIso S A c hc).hom.toHom.toCoordinateMap.comp
        ((q.baseChange S).atlas.transition A b c hb hc).hom.toHom.toCoordinateMap
    exact (congrArg₂ (fun F G : CoordinateMap A σ σ => F.comp G)
      (q.baseLeftTransition_coordinates S A b c hb hc)
      (q.baseChangeInvChartIso_coordinates S A b hb)).trans
      (((congrArg (fun f => f.hom.toHom.toCoordinateMap)
        (X.transition_cocycle (BasicAtlas.restrictTest S A)
          (q.baseSelectedSource S b) (q.baseOriginalSource S b) (q.baseOriginalSource S c)
          (q.baseSelected_unit S A b hb) (q.baseOriginal_unit S A b hb)
          (q.baseOriginal_unit S A c hc))).trans
        (congrArg (fun f => f.hom.toHom.toCoordinateMap)
          (X.transition_cocycle (BasicAtlas.restrictTest S A)
            (q.baseSelectedSource S b) (q.baseSelectedSource S c) (q.baseOriginalSource S c)
            (q.baseSelected_unit S A b hb) (q.baseSelected_unit S A c hc)
            (q.baseOriginal_unit S A c hc))).symm).trans
        (congrArg₂ (fun F G : CoordinateMap A σ σ => F.comp G)
          (q.baseChangeInvChartIso_coordinates S A c hc)
          (q.baseRightTransition_coordinates S A b c hb hc)).symm)

/-- Refinement and coefficient extension commute by a formal atlas isomorphism. -/
def baseChangeIso : Iso (q.atlas.baseChange S) (q.baseChange S).atlas rfl where
  hom := q.baseChangeHom S
  inv := q.baseChangeInv S
  inv_hom := by
    apply Hom.ext
    intro A b hb
    apply ModuleLaw.Hom.ext
    apply CommLaw.Hom.ext
    change (q.baseChangeInvChartIso S A b hb).hom.toHom.toCoordinateMap.comp
      (q.baseChangeChartIso S A b hb).hom.toHom.toCoordinateMap = CoordinateMap.id
    exact (congrArg₂ (fun F G : CoordinateMap A σ σ => F.comp G)
      (q.baseChangeInvChartIso_coordinates S A b hb)
      (q.baseChangeChartIso_coordinates S A b hb)).trans
      ((congrArg (fun f => f.hom.toHom.toCoordinateMap)
        (X.transition_cocycle (BasicAtlas.restrictTest S A)
          (q.baseOriginalSource S b) (q.baseSelectedSource S b) (q.baseOriginalSource S b)
          (q.baseOriginal_unit S A b hb) (q.baseSelected_unit S A b hb)
          (q.baseOriginal_unit S A b hb))).trans
        (congrArg (fun f => f.hom.toHom.toCoordinateMap)
          (X.transition_self (BasicAtlas.restrictTest S A) (q.baseOriginalSource S b)
            (q.baseOriginal_unit S A b hb))))
  hom_inv := by
    apply Hom.ext
    intro A b hb
    apply ModuleLaw.Hom.ext
    apply CommLaw.Hom.ext
    change (q.baseChangeChartIso S A b hb).hom.toHom.toCoordinateMap.comp
      (q.baseChangeInvChartIso S A b hb).hom.toHom.toCoordinateMap = CoordinateMap.id
    exact (congrArg₂ (fun F G : CoordinateMap A σ σ => F.comp G)
      (q.baseChangeChartIso_coordinates S A b hb)
      (q.baseChangeInvChartIso_coordinates S A b hb)).trans
      ((congrArg (fun f => f.hom.toHom.toCoordinateMap)
        (X.transition_cocycle (BasicAtlas.restrictTest S A)
          (q.baseSelectedSource S b) (q.baseOriginalSource S b) (q.baseSelectedSource S b)
          (q.baseSelected_unit S A b hb) (q.baseOriginal_unit S A b hb)
          (q.baseSelected_unit S A b hb))).trans
        (congrArg (fun f => f.hom.toHom.toCoordinateMap)
          (X.transition_self (BasicAtlas.restrictTest S A) (q.baseSelectedSource S b)
            (q.baseSelected_unit S A b hb))))

/-- The formal comparison identifies the two restrictions of every complete family. -/
theorem baseChange_onPoints (A : CommAlgCat.{v} S)
    (x : X.Point (BasicAtlas.restrictTest S A)) :
    (q.baseChangeIso S).onPoints A
      (q.atlas.toBaseChangePoints S A (q.onPoints (BasicAtlas.restrictTest S A) x)) =
        (q.baseChange S).onPoints A (X.toBaseChangePoints S A x) := by
  apply Subtype.ext
  funext t
  let z : SeriesPoint t.algebra σ Empty :=
    x.val ⟨BasicAtlas.restrictTest S t.algebra, restrictTestHom S t.map,
      q.baseOriginalSource S t.chart, q.baseOriginal_unit S t.algebra t.chart t.isUnit⟩
  change SeriesPoint.eval (q.baseChangeChartIso S t.algebra t.chart t.isUnit).hom.toHom.toCoordinateMap z =
    x.val ⟨BasicAtlas.restrictTest S t.algebra, restrictTestHom S t.map,
      q.baseSelectedSource S t.chart, q.baseSelected_unit S t.algebra t.chart t.isUnit⟩
  exact (congrArg (fun F : CoordinateMap t.algebra σ σ => SeriesPoint.eval F z)
    (q.baseChangeChartIso_coordinates S t.algebra t.chart t.isUnit)).trans
      (x.property.2 (BasicAtlas.restrictTest S t.algebra) (restrictTestHom S t.map)
        (q.baseOriginalSource S t.chart) (q.baseSelectedSource S t.chart)
        (q.baseOriginal_unit S t.algebra t.chart t.isUnit)
        (q.baseSelected_unit S t.algebra t.chart t.isUnit))

/-- The inverse formal comparison realizes the reverse complete-family square. -/
theorem baseChange_inv_onPoints (A : CommAlgCat.{v} S)
    (x : X.Point (BasicAtlas.restrictTest S A)) :
    ((q.baseChangeIso S).onPoints A).symm
      ((q.baseChange S).onPoints A (X.toBaseChangePoints S A x)) =
        q.atlas.toBaseChangePoints S A (q.onPoints (BasicAtlas.restrictTest S A) x) := by
  exact (LinearEquiv.symm_apply_eq ((q.baseChangeIso S).onPoints A)).mpr
    (q.baseChange_onPoints S A x).symm

end CoverRefinement

end Langlands.FormalGroup.ModuleLaw.BasicAtlas
