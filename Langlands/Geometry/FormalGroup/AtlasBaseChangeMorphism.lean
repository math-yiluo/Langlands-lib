import Langlands.Geometry.FormalGroup.AtlasBaseChangePoints
import Langlands.Geometry.FormalGroup.AtlasComparison

/-! # Coefficient extension of actual formal atlas morphisms -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ τ υ : Type} [Finite σ] [Finite τ] [Finite υ]
variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ} {Z : BasicAtlas O R υ}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- Equal original covers have equal image covers after coefficient extension. -/
theorem baseOpens_eq (S : CommAlgCat.{v} R) (h : X.opens = Y.opens) :
    (X.baseChange S).opens = (Y.baseChange S).opens :=
  congrArg (fun t : Set R => algebraMap R S '' t) h

/-- The choice of a preimage generator respects equality of the original generator sets. -/
theorem baseSource_sourceChart (S : CommAlgCat.{v} R) (h : X.opens = Y.opens)
    (b : Y.baseOpens S) :
    X.baseSource S (sourceChart (baseOpens_eq S h) b) =
      sourceChart h (Y.baseSource S b) := by
  apply Subtype.ext
  dsimp [baseSource]
  simp only [h]

/-- Reindexing equal original chart indices preserves their law on a coefficient test. -/
theorem testChart_eq (X : BasicAtlas O R σ) (A : CommAlgCat.{v} R)
    (a b : X.opens) (ha : IsUnit (algebraMap R A a.val))
    (hb : IsUnit (algebraMap R A b.val)) (e : a = b) :
    (X.chart a).map (coefficientLift (O := O) a.val A ha) =
      (X.chart b).map (coefficientLift (O := O) b.val A hb) := by
  cases e
  rfl

/-- Equal source and target indices give equal actual formal transition series. -/
theorem testTransition_coordinates_eq (X : BasicAtlas O R σ) (A : CommAlgCat.{v} R)
    (a b a' b' : X.opens) (ha : IsUnit (algebraMap R A a.val))
    (hb : IsUnit (algebraMap R A b.val)) (ha' : IsUnit (algebraMap R A a'.val))
    (hb' : IsUnit (algebraMap R A b'.val)) (ea : a = a') (eb : b = b') :
    (X.transition A a b ha hb).hom.toHom.toCoordinateMap =
      (X.transition A a' b' ha' hb').hom.toHom.toCoordinateMap := by
  cases ea
  cases eb
  rfl

/-- The source-chart comparison with indices transported across the equal covers. -/
def baseSourceChartIso (S : CommAlgCat.{v} R) (h : X.opens = Y.opens)
    (A : CommAlgCat.{v} S) (b : Y.baseOpens S)
    (hb : IsUnit (algebraMap S A b.val)) :
    ModuleLaw.Iso
      (((X.baseChange S).chart (sourceChart (baseOpens_eq S h) b)).map
        (coefficientLift (O := O) b.val A hb))
      ((X.chart (sourceChart h (Y.baseSource S b))).map
        (coefficientLift (O := O) (Y.baseSource S b).val (restrictTest S A)
          (Y.baseSource_unit S A b hb))) :=
  ModuleLaw.Iso.ofIdenticalCoordinates
    (by
      change ((X.chart (X.baseSource S (sourceChart (baseOpens_eq S h) b))).groupLaw.addition.map
        (X.baseChartCoefficient S (sourceChart (baseOpens_eq S h) b)).toRingHom).map
        (coefficientLift (O := O) b.val A hb).toRingHom = _
      rw [CoordinateMap.map_ringHom_comp]
      erw [X.baseCoefficient_comp S A (sourceChart (baseOpens_eq S h) b) hb]
      exact congrArg (fun F : ModuleLaw O (restrictTest S A) σ => F.groupLaw.addition)
        (X.testChart_eq (restrictTest S A) _ _ _ _ (baseSource_sourceChart S h b)))
    (fun a => by
      change (((X.chart (X.baseSource S (sourceChart (baseOpens_eq S h) b))).action a).toCoordinateMap.map
        (X.baseChartCoefficient S (sourceChart (baseOpens_eq S h) b)).toRingHom).map
        (coefficientLift (O := O) b.val A hb).toRingHom = _
      rw [CoordinateMap.map_ringHom_comp]
      erw [X.baseCoefficient_comp S A (sourceChart (baseOpens_eq S h) b) hb]
      exact congrArg (fun F : ModuleLaw O (restrictTest S A) σ => (F.action a).toCoordinateMap)
        (X.testChart_eq (restrictTest S A) _ _ _ _ (baseSource_sourceChart S h b)))

/-- Transported source indices preserve the original transition series. -/
theorem baseSourceTransition_coordinates (S : CommAlgCat.{v} R) (h : X.opens = Y.opens)
    (A : CommAlgCat.{v} S) (b c : Y.baseOpens S)
    (hb : IsUnit (algebraMap S A b.val)) (hc : IsUnit (algebraMap S A c.val)) :
    ((X.baseChange S).transition A (sourceChart (baseOpens_eq S h) b)
      (sourceChart (baseOpens_eq S h) c) hb hc).hom.toHom.toCoordinateMap =
      (X.transition (restrictTest S A) (sourceChart h (Y.baseSource S b))
        (sourceChart h (Y.baseSource S c))
        (Y.baseSource_unit S A b hb) (Y.baseSource_unit S A c hc)).hom.toHom.toCoordinateMap := by
  change (X.baseTransition S A (sourceChart (baseOpens_eq S h) b)
    (sourceChart (baseOpens_eq S h) c) hb hc).hom.toHom.toCoordinateMap = _
  erw [X.baseTransition_coordinates]
  exact X.testTransition_coordinates_eq (restrictTest S A) _ _ _ _ _ _ _ _
    (baseSource_sourceChart S h b) (baseSource_sourceChart S h c)

/-- Equal chart indices give the same component tuple of an actual family. -/
theorem family_chart_eq (X : BasicAtlas O R σ) {A : CommAlgCat.{v} R}
    (x : X.Point A) (B : CommAlgCat.{v} R) (φ : A ⟶ B) (a b : X.opens)
    (ha : IsUnit (algebraMap R B a.val)) (hb : IsUnit (algebraMap R B b.val))
    (e : a = b) :
    (x.val ⟨B, φ, a, ha⟩ : SeriesPoint B σ Empty) = x.val ⟨B, φ, b, hb⟩ := by
  cases e
  rfl

namespace Hom

variable {h : X.opens = Y.opens} {k : Y.opens = Z.opens}

/-- Conjugate an actual chart map by the identity-coordinate coefficient comparisons. -/
def baseChartHom (f : Hom X Y h) (S : CommAlgCat.{v} R)
    (A : CommAlgCat.{v} S) (b : Y.baseOpens S)
    (hb : IsUnit (algebraMap S A b.val)) :
    ModuleLaw.Hom
      (((X.baseChange S).chart (sourceChart (baseOpens_eq S h) b)).map
        (coefficientLift (O := O) b.val A hb))
      (((Y.baseChange S).chart b).map (coefficientLift (O := O) b.val A hb)) :=
  (Y.baseChartIso S A b hb).inv.comp
    ((f.hom (restrictTest S A) (Y.baseSource S b) (Y.baseSource_unit S A b hb)).comp
      (baseSourceChartIso S h A b hb).hom)

/-- The extended formal map has the original map's actual coordinate series. -/
@[simp]
theorem baseChartHom_coordinates (f : Hom X Y h) (S : CommAlgCat.{v} R)
    (A : CommAlgCat.{v} S) (b : Y.baseOpens S)
    (hb : IsUnit (algebraMap S A b.val)) :
    (f.baseChartHom S A b hb).toHom.toCoordinateMap =
      (f.hom (restrictTest S A) (Y.baseSource S b)
        (Y.baseSource_unit S A b hb)).toHom.toCoordinateMap := by
  change CoordinateMap.id.comp
    ((f.hom (restrictTest S A) (Y.baseSource S b)
      (Y.baseSource_unit S A b hb)).toHom.toCoordinateMap.comp CoordinateMap.id) = _
  rw [CoordinateMap.id_comp, CoordinateMap.comp_id]

/-- Extend actual formal maps along an arbitrary change of coefficient algebra. -/
def baseChange (f : Hom X Y h) (S : CommAlgCat.{v} R) :
    Hom (X.baseChange S) (Y.baseChange S) (baseOpens_eq S h) where
  hom := f.baseChartHom S
  natural φ b ha hb := by
    change (CoordinateMap.id.comp
      ((f.hom (restrictTest S _) (Y.baseSource S b)
        (Y.baseSource_unit S _ b ha)).toHom.toCoordinateMap.comp CoordinateMap.id)).map
          φ.hom.toRingHom =
      CoordinateMap.id.comp
        ((f.hom (restrictTest S _) (Y.baseSource S b)
          (Y.baseSource_unit S _ b hb)).toHom.toCoordinateMap.comp CoordinateMap.id)
    simp only [CoordinateMap.id_comp, CoordinateMap.comp_id]
    exact f.natural (restrictTestHom S φ) (Y.baseSource S b)
      (Y.baseSource_unit S _ b ha) (Y.baseSource_unit S _ b hb)
  transition A b c hb hc := by
    apply ModuleLaw.Hom.ext
    apply CommLaw.Hom.ext
    change ((Y.baseChange S).transition A b c hb hc).hom.toHom.toCoordinateMap.comp
      (CoordinateMap.id.comp
        ((f.hom (restrictTest S A) (Y.baseSource S b) _).toHom.toCoordinateMap.comp
          CoordinateMap.id)) =
      (CoordinateMap.id.comp
        ((f.hom (restrictTest S A) (Y.baseSource S c) _).toHom.toCoordinateMap.comp
          CoordinateMap.id)).comp
        ((X.baseChange S).transition A (sourceChart (baseOpens_eq S h) b)
          (sourceChart (baseOpens_eq S h) c) hb hc).hom.toHom.toCoordinateMap
    simp only [CoordinateMap.id_comp, CoordinateMap.comp_id]
    exact (congrArg (fun T : CoordinateMap A τ τ => T.comp
      (f.hom (restrictTest S A) (Y.baseSource S b) _).toHom.toCoordinateMap)
        (Y.baseTransition_coordinates S A b c hb hc)).trans
      ((congrArg (fun g => g.toHom.toCoordinateMap)
        (f.transition (restrictTest S A) (Y.baseSource S b) (Y.baseSource S c)
          (Y.baseSource_unit S A b hb) (Y.baseSource_unit S A c hc))).trans
        (congrArg (fun T : CoordinateMap A σ σ =>
          (f.hom (restrictTest S A) (Y.baseSource S c) _).toHom.toCoordinateMap.comp T)
            (baseSourceTransition_coordinates S h A b c hb hc)).symm)

/-- Coefficient extension leaves the original formal coordinate series unchanged. -/
@[simp]
theorem baseChange_coordinates (f : Hom X Y h) (S : CommAlgCat.{v} R)
    (A : CommAlgCat.{v} S) (b : Y.baseOpens S)
    (hb : IsUnit (algebraMap S A b.val)) :
    ((f.baseChange S).hom A b hb).toHom.toCoordinateMap =
      (f.hom (restrictTest S A) (Y.baseSource S b)
        (Y.baseSource_unit S A b hb)).toHom.toCoordinateMap :=
  f.baseChartHom_coordinates S A b hb

/-- Coefficient extension preserves identity formal maps. -/
@[simp]
theorem baseChange_id (X : BasicAtlas O R σ) (S : CommAlgCat.{v} R) :
    (Hom.id X).baseChange S = Hom.id (X.baseChange S) := by
  apply Hom.ext
  intro A b hb
  apply ModuleLaw.Hom.ext
  apply CommLaw.Hom.ext
  change CoordinateMap.id.comp (CoordinateMap.id.comp CoordinateMap.id) = CoordinateMap.id
  simp only [CoordinateMap.id_comp]

/-- Reindexing equal charts preserves the actual formal map series. -/
theorem hom_coordinates_eq (f : Hom X Y h) (A : CommAlgCat.{v} R)
    (a b : Y.opens) (ha : IsUnit (algebraMap R A a.val))
    (hb : IsUnit (algebraMap R A b.val)) (e : a = b) :
    (f.hom A a ha).toHom.toCoordinateMap = (f.hom A b hb).toHom.toCoordinateMap := by
  cases e
  rfl

/-- Coefficient extension preserves actual formal composition. -/
@[simp]
theorem baseChange_comp (g : Hom Y Z k) (f : Hom X Y h) (S : CommAlgCat.{v} R) :
    (g.comp f).baseChange S = (g.baseChange S).comp (f.baseChange S) := by
  apply Hom.ext
  intro A b hb
  apply ModuleLaw.Hom.ext
  apply CommLaw.Hom.ext
  change CoordinateMap.id.comp
    (((g.hom (restrictTest S A) (Z.baseSource S b) _).toHom.toCoordinateMap.comp
      (f.hom (restrictTest S A) (sourceChart k (Z.baseSource S b)) _).toHom.toCoordinateMap).comp
        CoordinateMap.id) =
    (CoordinateMap.id.comp
      ((g.hom (restrictTest S A) (Z.baseSource S b) _).toHom.toCoordinateMap.comp
        CoordinateMap.id)).comp
      (CoordinateMap.id.comp
        ((f.hom (restrictTest S A) (Y.baseSource S (sourceChart (baseOpens_eq S k) b)) _).toHom.toCoordinateMap.comp
          CoordinateMap.id))
  simp only [CoordinateMap.id_comp, CoordinateMap.comp_id]
  exact congrArg (fun F : CoordinateMap A σ τ => (g.hom (restrictTest S A) (Z.baseSource S b) _).toHom.toCoordinateMap.comp F)
    (f.hom_coordinates_eq (restrictTest S A) _ _ _ _ (baseSource_sourceChart S k b)).symm

/-- Extending the formal map commutes with the full compatible-family comparison. -/
theorem baseChange_onPoints (f : Hom X Y h) (S : CommAlgCat.{v} R)
    (A : CommAlgCat.{v} S) (x : X.Point (restrictTest S A)) :
    (f.baseChange S).onPoints A (X.toBaseChangePoints S A x) =
      Y.toBaseChangePoints S A (f.onPoints (restrictTest S A) x) := by
  apply Subtype.ext
  funext t
  change SeriesPoint.eval
    (CoordinateMap.id.comp
      ((f.hom (restrictTest S t.algebra) (Y.baseSource S t.chart)
        (Y.baseSource_unit S t.algebra t.chart t.isUnit)).toHom.toCoordinateMap.comp
          CoordinateMap.id))
    (x.val ⟨restrictTest S t.algebra, restrictTestHom S t.map,
      X.baseSource S (sourceChart (baseOpens_eq S h) t.chart),
        X.baseSource_unit S t.algebra (sourceChart (baseOpens_eq S h) t.chart) t.isUnit⟩) =
    SeriesPoint.eval
      (f.hom (restrictTest S t.algebra) (Y.baseSource S t.chart)
        (Y.baseSource_unit S t.algebra t.chart t.isUnit)).toHom.toCoordinateMap
      (x.val ⟨restrictTest S t.algebra, restrictTestHom S t.map,
        sourceChart h (Y.baseSource S t.chart), Y.baseSource_unit S t.algebra t.chart t.isUnit⟩)
  simp only [CoordinateMap.id_comp, CoordinateMap.comp_id]
  exact congrArg (fun z : SeriesPoint t.algebra σ Empty =>
    SeriesPoint.eval
      (f.hom (restrictTest S t.algebra) (Y.baseSource S t.chart)
        (Y.baseSource_unit S t.algebra t.chart t.isUnit)).toHom.toCoordinateMap z)
    (X.family_chart_eq x (restrictTest S t.algebra) (restrictTestHom S t.map) _ _ _ _
      (baseSource_sourceChart S h t.chart))

/-- The constructed inverse family comparison also commutes with the formal map. -/
theorem baseChange_fromPoints (f : Hom X Y h) (S : CommAlgCat.{v} R)
    (A : CommAlgCat.{v} S) (y : (X.baseChange S).Point A) :
    f.onPoints (restrictTest S A) (X.fromBaseChangePoints S A y) =
      Y.fromBaseChangePoints S A ((f.baseChange S).onPoints A y) := by
  apply (Y.baseChangePointEquiv S A).injective
  change Y.toBaseChangePoints S A
    (f.onPoints (restrictTest S A) (X.fromBaseChangePoints S A y)) =
    Y.toBaseChangePoints S A (Y.fromBaseChangePoints S A ((f.baseChange S).onPoints A y))
  rw [← f.baseChange_onPoints, X.to_fromBaseChangePoints, Y.to_fromBaseChangePoints]

end Hom

namespace Iso

variable {h : X.opens = Y.opens}

/-- Extend both actual formal maps, retaining their formal inverse equations. -/
def baseChange (f : Iso X Y h) (S : CommAlgCat.{v} R) :
    Iso (X.baseChange S) (Y.baseChange S) (baseOpens_eq S h) where
  hom := f.hom.baseChange S
  inv := f.inv.baseChange S
  inv_hom := (Hom.baseChange_comp f.inv f.hom S).symm.trans
    ((congrArg (fun g => g.baseChange S) f.inv_hom).trans (Hom.baseChange_id X S))
  hom_inv := (Hom.baseChange_comp f.hom f.inv S).symm.trans
    ((congrArg (fun g => g.baseChange S) f.hom_inv).trans (Hom.baseChange_id Y S))

/-- The extended formal isomorphism realizes the same full-family comparison square. -/
theorem baseChange_onPoints (f : Iso X Y h) (S : CommAlgCat.{v} R)
    (A : CommAlgCat.{v} S) (x : X.Point (restrictTest S A)) :
    (f.baseChange S).onPoints A (X.baseChangePointEquiv S A x) =
      Y.baseChangePointEquiv S A (f.onPoints (restrictTest S A) x) :=
  f.hom.baseChange_onPoints S A x

end Iso

end Langlands.FormalGroup.ModuleLaw.BasicAtlas
