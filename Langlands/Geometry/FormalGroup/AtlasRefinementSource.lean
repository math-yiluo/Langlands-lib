import Langlands.Geometry.FormalGroup.AtlasRefinementComposition

/-! # Formal comparison of source-chart selections on a finer cover -/

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
variable (q r : CoverRefinement X) (h : q.opens = r.opens)

/-- Compare the two selected original laws by their actual formal transition. -/
def sourceChartIso (A : CommAlgCat.{v} R) (b : r.opens)
    (hb : IsUnit (algebraMap R A b.val)) :
    ModuleLaw.Iso
      ((q.chart (sourceChart (X := q.atlas) (Y := r.atlas) h b)).map (coefficientLift (O := O) b.val A hb))
      ((r.chart b).map (coefficientLift (O := O) b.val A hb)) :=
  (q.chartIso A (sourceChart (X := q.atlas) (Y := r.atlas) h b) hb).trans
    ((X.transition A (q.source (sourceChart (X := q.atlas) (Y := r.atlas) h b)) (r.source b)
      (q.source_unit A (sourceChart (X := q.atlas) (Y := r.atlas) h b) hb) (r.source_unit A b hb)).trans
        (r.chartIso A b hb).symm)

/-- The comparison retains the actual transition between the original source charts. -/
theorem sourceChartIso_coordinates (A : CommAlgCat.{v} R) (b : r.opens)
    (hb : IsUnit (algebraMap R A b.val)) :
    (q.sourceChartIso r h A b hb).hom.toHom.toCoordinateMap =
      (X.transition A (q.source (sourceChart (X := q.atlas) (Y := r.atlas) h b)) (r.source b)
        (q.source_unit A (sourceChart (X := q.atlas) (Y := r.atlas) h b) hb)
        (r.source_unit A b hb)).hom.toHom.toCoordinateMap := by
  change (CoordinateMap.id.comp
    (X.transition A (q.source (sourceChart (X := q.atlas) (Y := r.atlas) h b)) (r.source b)
      (q.source_unit A (sourceChart (X := q.atlas) (Y := r.atlas) h b) hb)
      (r.source_unit A b hb)).hom.toHom.toCoordinateMap).comp CoordinateMap.id = _
  simp only [CoordinateMap.id_comp, CoordinateMap.comp_id]

/-- Source-chart choices on an equal finer cover give an actual formal atlas map. -/
def sourceHom : Hom q.atlas r.atlas h where
  hom A b hb := (q.sourceChartIso r h A b hb).hom
  natural φ b ha hb := by
    change ((CoordinateMap.id.comp
      (X.transition _ (q.source (sourceChart (X := q.atlas) (Y := r.atlas) h b)) (r.source b)
        (q.source_unit _ (sourceChart (X := q.atlas) (Y := r.atlas) h b) ha)
        (r.source_unit _ b ha)).hom.toHom.toCoordinateMap).comp CoordinateMap.id).map
          φ.hom.toRingHom =
      (CoordinateMap.id.comp
        (X.transition _ (q.source (sourceChart (X := q.atlas) (Y := r.atlas) h b)) (r.source b)
          (q.source_unit _ (sourceChart (X := q.atlas) (Y := r.atlas) h b) hb)
          (r.source_unit _ b hb)).hom.toHom.toCoordinateMap).comp CoordinateMap.id
    simp only [CoordinateMap.id_comp, CoordinateMap.comp_id]
    exact X.transition_natural φ _ _ _ _ _ _
  transition A b c hb hc := by
    apply ModuleLaw.Hom.ext
    apply CommLaw.Hom.ext
    change
      ((CoordinateMap.id.comp
        (X.transition A (r.source b) (r.source c)
          (r.source_unit A b hb) (r.source_unit A c hc)).hom.toHom.toCoordinateMap).comp
            CoordinateMap.id).comp
        ((CoordinateMap.id.comp
          (X.transition A (q.source (sourceChart (X := q.atlas) (Y := r.atlas) h b)) (r.source b)
            (q.source_unit A (sourceChart (X := q.atlas) (Y := r.atlas) h b) hb)
            (r.source_unit A b hb)).hom.toHom.toCoordinateMap).comp CoordinateMap.id) =
      ((CoordinateMap.id.comp
        (X.transition A (q.source (sourceChart (X := q.atlas) (Y := r.atlas) h c)) (r.source c)
          (q.source_unit A (sourceChart (X := q.atlas) (Y := r.atlas) h c) hc)
          (r.source_unit A c hc)).hom.toHom.toCoordinateMap).comp CoordinateMap.id).comp
        ((CoordinateMap.id.comp
          (X.transition A (q.source (sourceChart (X := q.atlas) (Y := r.atlas) h b)) (q.source (sourceChart (X := q.atlas) (Y := r.atlas) h c))
            (q.source_unit A (sourceChart (X := q.atlas) (Y := r.atlas) h b) hb)
            (q.source_unit A (sourceChart (X := q.atlas) (Y := r.atlas) h c) hc)).hom.toHom.toCoordinateMap).comp
              CoordinateMap.id)
    simp only [CoordinateMap.id_comp, CoordinateMap.comp_id]
    exact (congrArg (fun f => f.hom.toHom.toCoordinateMap)
      (X.transition_cocycle A (q.source (sourceChart (X := q.atlas) (Y := r.atlas) h b)) (r.source b) (r.source c)
        (q.source_unit A (sourceChart (X := q.atlas) (Y := r.atlas) h b) hb)
        (r.source_unit A b hb) (r.source_unit A c hc))).trans
      (congrArg (fun f => f.hom.toHom.toCoordinateMap)
        (X.transition_cocycle A (q.source (sourceChart (X := q.atlas) (Y := r.atlas) h b))
          (q.source (sourceChart (X := q.atlas) (Y := r.atlas) h c)) (r.source c)
          (q.source_unit A (sourceChart (X := q.atlas) (Y := r.atlas) h b) hb)
          (q.source_unit A (sourceChart (X := q.atlas) (Y := r.atlas) h c) hc) (r.source_unit A c hc))).symm

/-- The source-choice atlas map has exactly the original transition coordinates. -/
theorem sourceHom_coordinates (A : CommAlgCat.{v} R) (b : r.opens)
    (hb : IsUnit (algebraMap R A b.val)) :
    ((q.sourceHom r h).hom A b hb).toHom.toCoordinateMap =
      (X.transition A (q.source (sourceChart (X := q.atlas) (Y := r.atlas) h b)) (r.source b)
        (q.source_unit A (sourceChart (X := q.atlas) (Y := r.atlas) h b) hb)
        (r.source_unit A b hb)).hom.toHom.toCoordinateMap :=
  q.sourceChartIso_coordinates r h A b hb

/-- Comparing the same selection with itself is the identity formal map. -/
theorem sourceHom_id : q.sourceHom q rfl = Hom.id q.atlas := by
  apply Hom.ext
  intro A b hb
  apply ModuleLaw.Hom.ext
  apply CommLaw.Hom.ext
  exact (q.sourceHom_coordinates q rfl A b hb).trans
    (congrArg (fun f => f.hom.toHom.toCoordinateMap)
      (X.transition_self A (q.source b) (q.source_unit A b hb)))

/-- Successive changes of source charts equal the direct formal comparison. -/
theorem sourceHom_comp (s : CoverRefinement X) (k : r.opens = s.opens) :
    (r.sourceHom s k).comp (q.sourceHom r h) =
      q.sourceHom s (h.trans k) := by
  apply Hom.ext
  intro A b hb
  apply ModuleLaw.Hom.ext
  apply CommLaw.Hom.ext
  change
    ((CoordinateMap.id.comp
      (X.transition A (r.source (sourceChart (X := r.atlas) (Y := s.atlas) k b)) (s.source b)
        (r.source_unit A (sourceChart (X := r.atlas) (Y := s.atlas) k b) hb)
        (s.source_unit A b hb)).hom.toHom.toCoordinateMap).comp CoordinateMap.id).comp
      ((CoordinateMap.id.comp
        (X.transition A (q.source (sourceChart (X := q.atlas) (Y := s.atlas) (h.trans k) b))
          (r.source (sourceChart (X := r.atlas) (Y := s.atlas) k b))
          (q.source_unit A (sourceChart (X := q.atlas) (Y := s.atlas) (h.trans k) b) hb)
          (r.source_unit A (sourceChart (X := r.atlas) (Y := s.atlas) k b) hb)).hom.toHom.toCoordinateMap).comp
            CoordinateMap.id) =
    (CoordinateMap.id.comp
      (X.transition A (q.source (sourceChart (X := q.atlas) (Y := s.atlas) (h.trans k) b)) (s.source b)
        (q.source_unit A (sourceChart (X := q.atlas) (Y := s.atlas) (h.trans k) b) hb)
        (s.source_unit A b hb)).hom.toHom.toCoordinateMap).comp CoordinateMap.id
  simp only [CoordinateMap.id_comp, CoordinateMap.comp_id]
  exact congrArg (fun f => f.hom.toHom.toCoordinateMap)
    (X.transition_cocycle A (q.source (sourceChart (X := q.atlas) (Y := s.atlas) (h.trans k) b))
      (r.source (sourceChart (X := r.atlas) (Y := s.atlas) k b)) (s.source b)
      (q.source_unit A (sourceChart (X := q.atlas) (Y := s.atlas) (h.trans k) b) hb)
      (r.source_unit A (sourceChart (X := r.atlas) (Y := s.atlas) k b) hb) (s.source_unit A b hb))

/-- Different source-chart selections on the same finer cover are formally isomorphic. -/
def sourceIso : Iso q.atlas r.atlas h where
  hom := q.sourceHom r h
  inv := r.sourceHom q h.symm
  inv_hom := (q.sourceHom_comp r h q h.symm).trans q.sourceHom_id
  hom_inv := (r.sourceHom_comp q h.symm r h).trans r.sourceHom_id

/-- The formal source comparison identifies restrictions of every original family. -/
theorem source_onPoints (A : CommAlgCat.{v} R) (x : X.Point A) :
    (q.sourceIso r h).hom.onPoints A (q.onPoints A x) = r.onPoints A x := by
  apply Subtype.ext
  funext t
  let z : SeriesPoint t.algebra σ Empty :=
    x.val ⟨t.algebra, t.map, q.source (sourceChart (X := q.atlas) (Y := r.atlas) h t.chart),
      q.source_unit t.algebra (sourceChart (X := q.atlas) (Y := r.atlas) h t.chart) t.isUnit⟩
  change SeriesPoint.eval
    ((q.sourceHom r h).hom t.algebra t.chart t.isUnit).toHom.toCoordinateMap z =
      x.val ⟨t.algebra, t.map, r.source t.chart,
        r.source_unit t.algebra t.chart t.isUnit⟩
  exact (congrArg (fun F : CoordinateMap t.algebra σ σ => SeriesPoint.eval F z)
    (q.sourceHom_coordinates r h t.algebra t.chart t.isUnit)).trans
      (x.property.2 t.algebra t.map (q.source (sourceChart (X := q.atlas) (Y := r.atlas) h t.chart))
        (r.source t.chart)
        (q.source_unit t.algebra (sourceChart (X := q.atlas) (Y := r.atlas) h t.chart) t.isUnit)
        (r.source_unit t.algebra t.chart t.isUnit))

end CoverRefinement

end Langlands.FormalGroup.ModuleLaw.BasicAtlas
