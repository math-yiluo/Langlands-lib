import Langlands.Geometry.FormalGroup.AtlasComparison

/-! # Formal morphisms on finer principal covers -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ τ υ : Type} [Finite σ] [Finite τ] [Finite υ]

attribute [local instance] coefficientAlgebra coefficientScalarTower

namespace CoverRefinement

variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ}

/-- Carry the selected source charts across an equality of original covers. -/
def retarget (q : CoverRefinement X) (Y : BasicAtlas O R τ)
    (h : X.opens = Y.opens) : CoverRefinement Y where
  opens := q.opens
  covers := q.covers
  source b := sourceChart h.symm (q.source b)
  contains := q.contains

end CoverRefinement

namespace Hom

variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ} {Z : BasicAtlas O R υ}
variable {h : X.opens = Y.opens} {k : Y.opens = Z.opens}

/-- Restrict each actual formal map using the identity-coordinate chart isomorphisms. -/
def restrict (f : Hom X Y h) (q : CoverRefinement X) :
    Hom q.atlas (q.retarget Y h).atlas rfl where
  hom A b hb :=
    ((q.retarget Y h).chartIso A b hb).inv.comp
      ((f.hom A (sourceChart h.symm (q.source b)) (q.source_unit A b hb)).comp
        (q.chartIso A b hb).hom)
  natural φ b ha hb := by
    change
      (CoordinateMap.id.comp
        ((f.hom _ (sourceChart h.symm (q.source b)) (q.source_unit _ b ha)).toHom.toCoordinateMap.comp
          CoordinateMap.id)).map φ.hom.toRingHom =
      CoordinateMap.id.comp
        ((f.hom _ (sourceChart h.symm (q.source b)) (q.source_unit _ b hb)).toHom.toCoordinateMap.comp
          CoordinateMap.id)
    simp only [CoordinateMap.id_comp, CoordinateMap.comp_id]
    exact f.natural φ _ _ _
  transition A b c hb hc := by
    apply ModuleLaw.Hom.ext
    apply CommLaw.Hom.ext
    change ((q.retarget Y h).transition A b c hb hc).hom.toHom.toCoordinateMap.comp
      (CoordinateMap.id.comp
        ((f.hom A (sourceChart h.symm (q.source b)) (q.source_unit A b hb)).toHom.toCoordinateMap.comp
          CoordinateMap.id)) =
      (CoordinateMap.id.comp
        ((f.hom A (sourceChart h.symm (q.source c)) (q.source_unit A c hc)).toHom.toCoordinateMap.comp
          CoordinateMap.id)).comp (q.transition A b c hb hc).hom.toHom.toCoordinateMap
    simp only [CoordinateMap.id_comp, CoordinateMap.comp_id]
    change ((CoordinateMap.id.comp
      (Y.transition A (sourceChart h.symm (q.source b)) (sourceChart h.symm (q.source c))
        (q.source_unit A b hb) (q.source_unit A c hc)).hom.toHom.toCoordinateMap).comp
          CoordinateMap.id).comp
        (f.hom A (sourceChart h.symm (q.source b)) _).toHom.toCoordinateMap =
      (f.hom A (sourceChart h.symm (q.source c)) _).toHom.toCoordinateMap.comp
        ((CoordinateMap.id.comp
          (X.transition A (q.source b) (q.source c)
            (q.source_unit A b hb) (q.source_unit A c hc)).hom.toHom.toCoordinateMap).comp
              CoordinateMap.id)
    simp only [CoordinateMap.id_comp, CoordinateMap.comp_id]
    exact congrArg (fun g => g.toHom.toCoordinateMap)
      (f.transition A (sourceChart h.symm (q.source b))
        (sourceChart h.symm (q.source c)) (q.source_unit A b hb) (q.source_unit A c hc))

/-- Coefficient restriction leaves the actual formal coordinate series unchanged. -/
@[simp]
theorem restrict_coordinates (f : Hom X Y h) (q : CoverRefinement X)
    (A : CommAlgCat.{v} R) (b : q.opens) (hb : IsUnit (algebraMap R A b.val)) :
    ((f.restrict q).hom A b hb).toHom.toCoordinateMap =
      (f.hom A (sourceChart h.symm (q.source b)) (q.source_unit A b hb)).toHom.toCoordinateMap := by
  change CoordinateMap.id.comp
    ((f.hom A (sourceChart h.symm (q.source b)) (q.source_unit A b hb)).toHom.toCoordinateMap.comp
      CoordinateMap.id) = _
  rw [CoordinateMap.id_comp, CoordinateMap.comp_id]

/-- Restriction preserves identity formal maps. -/
@[simp]
theorem restrict_id (X : BasicAtlas O R σ) (q : CoverRefinement X) :
    (Hom.id X).restrict q = Hom.id q.atlas := by
  apply Hom.ext
  intro A b hb
  apply ModuleLaw.Hom.ext
  apply CommLaw.Hom.ext
  change CoordinateMap.id.comp (CoordinateMap.id.comp CoordinateMap.id) = CoordinateMap.id
  simp only [CoordinateMap.id_comp]

/-- Restriction preserves formal composition, including the selected source charts. -/
@[simp]
theorem restrict_comp (g : Hom Y Z k) (f : Hom X Y h) (q : CoverRefinement X) :
    (g.comp f).restrict q = (g.restrict (q.retarget Y h)).comp (f.restrict q) := by
  apply Hom.ext
  intro A b hb
  apply ModuleLaw.Hom.ext
  apply CommLaw.Hom.ext
  change CoordinateMap.id.comp
    (((g.hom A (sourceChart (h.trans k).symm (q.source b)) _).toHom.toCoordinateMap.comp
      (f.hom A (sourceChart h.symm (q.source b)) _).toHom.toCoordinateMap).comp
        CoordinateMap.id) =
    (CoordinateMap.id.comp
      ((g.hom A (sourceChart (h.trans k).symm (q.source b)) _).toHom.toCoordinateMap.comp
        CoordinateMap.id)).comp
      (CoordinateMap.id.comp
        ((f.hom A (sourceChart h.symm (q.source b)) _).toHom.toCoordinateMap.comp CoordinateMap.id))
  simp only [CoordinateMap.id_comp, CoordinateMap.comp_id]

/-- Evaluation of a restricted formal map commutes with restriction of full families. -/
theorem restrict_onPoints (f : Hom X Y h) (q : CoverRefinement X)
    (A : CommAlgCat.{v} R) (x : X.Point A) :
    (f.restrict q).onPoints A (q.onPoints A x) =
      (q.retarget Y h).onPoints A (f.onPoints A x) := by
  apply Subtype.ext
  funext t
  let z : SeriesPoint t.algebra σ Empty :=
    x.val ⟨t.algebra, t.map, q.source t.chart, q.source_unit t.algebra t.chart t.isUnit⟩
  change SeriesPoint.eval ((f.restrict q).hom t.algebra t.chart t.isUnit).toHom.toCoordinateMap z =
    SeriesPoint.eval
      (f.hom t.algebra (sourceChart h.symm (q.source t.chart)) _).toHom.toCoordinateMap z
  exact congrArg (fun F : CoordinateMap t.algebra σ τ => SeriesPoint.eval F z)
      (f.restrict_coordinates q t.algebra t.chart t.isUnit)

end Hom

namespace Iso

variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ}
variable {h : X.opens = Y.opens}

/-- Restrict formal inverse maps to the selected finer charts. -/
def restrict (f : Iso X Y h) (q : CoverRefinement X) :
    Iso q.atlas (q.retarget Y h).atlas rfl where
  hom := f.hom.restrict q
  inv := f.inv.restrict (q.retarget Y h)
  inv_hom := by
    exact (Hom.restrict_comp f.inv f.hom q).symm.trans
      ((congrArg (fun g => g.restrict q) f.inv_hom).trans (Hom.restrict_id X q))
  hom_inv := by
    exact (Hom.restrict_comp f.hom f.inv (q.retarget Y h)).symm.trans
      ((congrArg (fun g => g.restrict (q.retarget Y h)) f.hom_inv).trans
        (Hom.restrict_id Y (q.retarget Y h)))

end Iso

end Langlands.FormalGroup.ModuleLaw.BasicAtlas
