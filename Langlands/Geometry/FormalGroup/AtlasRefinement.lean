import Langlands.Geometry.FormalGroup.BasicAtlas

/-! # Restriction of varying formal laws to a finer principal cover -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ : Type} [Finite σ]

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- A finer principal cover, with an actual localization containment in a chosen
original chart for every new chart. -/
structure CoverRefinement (X : BasicAtlas O R σ) where
  opens : Set R
  covers : Ideal.span opens = ⊤
  source : opens → X.opens
  contains : ∀ b : opens,
    IsUnit (algebraMap R (Localization.Away b.val) (source b).val)

namespace CoverRefinement

variable {X : BasicAtlas O R σ} (q : CoverRefinement X)

/-- The chosen original chart is defined over every test of the finer chart. -/
theorem source_unit (A : CommAlgCat.{v} R) (b : q.opens)
    (hb : IsUnit (algebraMap R A b.val)) :
    IsUnit (algebraMap R A (q.source b).val) := by
  have h := (q.contains b).map (coefficientLift (O := O) b.val A hb).toRingHom
  change IsUnit (coefficientLift (O := O) b.val A hb
    (algebraMap R (Localization.Away b.val) (q.source b).val)) at h
  rwa [coefficientLift_algebraMap] at h

/-- The actual coefficient map from the old chart to the finer localization. -/
def chartCoefficient (b : q.opens) :
    Localization.Away (q.source b).val →ₐ[O] Localization.Away b.val :=
  IsLocalization.Away.liftAlgHom (q.source b).val
    (f := IsScalarTower.toAlgHom O R (Localization.Away b.val)) (q.contains b)

@[simp]
theorem chartCoefficient_algebraMap (b : q.opens) (r : R) :
    q.chartCoefficient b (algebraMap R (Localization.Away (q.source b).val) r) =
      algebraMap R (Localization.Away b.val) r :=
  IsLocalization.Away.lift_eq (q.source b).val (q.contains b) r

/-- Uniqueness of localization maps identifies the two coefficient routes. -/
theorem coefficient_comp (A : CommAlgCat.{v} R) (b : q.opens)
    (hb : IsUnit (algebraMap R A b.val)) :
    (coefficientLift (O := O) b.val A hb).toRingHom.comp
        (q.chartCoefficient b).toRingHom =
      (coefficientLift (O := O) (q.source b).val A (q.source_unit A b hb)).toRingHom := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (q.source b).val)
  ext r
  change coefficientLift (O := O) b.val A hb
    (q.chartCoefficient b (algebraMap R (Localization.Away (q.source b).val) r)) =
      coefficientLift (O := O) (q.source b).val A (q.source_unit A b hb)
        (algebraMap R (Localization.Away (q.source b).val) r)
  rw [chartCoefficient_algebraMap, coefficientLift_algebraMap,
    coefficientLift_algebraMap]

/-- Restrict the actual chosen chart law to the finer principal localization. -/
def chart (b : q.opens) : ModuleLaw O (Localization.Away b.val) σ :=
  (X.chart (q.source b)).map (q.chartCoefficient b)

/-- The restricted law over a test is the original law with identical coordinates. -/
def chartIso (A : CommAlgCat.{v} R) (b : q.opens)
    (hb : IsUnit (algebraMap R A b.val)) :
    Iso ((q.chart b).map (coefficientLift (O := O) b.val A hb))
      ((X.chart (q.source b)).map
        (coefficientLift (O := O) (q.source b).val A (q.source_unit A b hb))) :=
  Iso.ofIdenticalCoordinates
    (by
      change ((X.chart (q.source b)).groupLaw.addition.map
        (q.chartCoefficient b).toRingHom).map
        (coefficientLift (O := O) b.val A hb).toRingHom = _
      rw [CoordinateMap.map_ringHom_comp, q.coefficient_comp]
      rfl)
    (fun a => by
      change (((X.chart (q.source b)).action a).toCoordinateMap.map
        (q.chartCoefficient b).toRingHom).map
        (coefficientLift (O := O) b.val A hb).toRingHom = _
      rw [CoordinateMap.map_ringHom_comp, q.coefficient_comp]
      rfl)

/-- Conjugate the original formal transition by the actual chart identifications. -/
def transition (A : CommAlgCat.{v} R) (a b : q.opens)
    (ha : IsUnit (algebraMap R A a.val)) (hb : IsUnit (algebraMap R A b.val)) :
    Iso ((q.chart a).map (coefficientLift (O := O) a.val A ha))
      ((q.chart b).map (coefficientLift (O := O) b.val A hb)) :=
  (q.chartIso A a ha).trans
    ((X.transition A (q.source a) (q.source b) (q.source_unit A a ha)
      (q.source_unit A b hb)).trans (q.chartIso A b hb).symm)

/-- Refinement does not alter the coordinate series of the original transition. -/
@[simp]
theorem transition_coordinates (A : CommAlgCat.{v} R) (a b : q.opens)
    (ha : IsUnit (algebraMap R A a.val)) (hb : IsUnit (algebraMap R A b.val)) :
    (q.transition A a b ha hb).hom.toHom.toCoordinateMap =
      (X.transition A (q.source a) (q.source b) (q.source_unit A a ha)
        (q.source_unit A b hb)).hom.toHom.toCoordinateMap := by
  change (CoordinateMap.id.comp
    (X.transition A (q.source a) (q.source b) (q.source_unit A a ha)
      (q.source_unit A b hb)).hom.toHom.toCoordinateMap).comp CoordinateMap.id = _
  rw [CoordinateMap.id_comp, CoordinateMap.comp_id]

/-- The actual atlas of restricted, possibly varying chart laws on the finer cover. -/
def atlas : BasicAtlas O R σ where
  opens := q.opens
  covers := q.covers
  chart := q.chart
  transition := q.transition
  transition_self A a ha := by
    apply Iso.ext_hom
    apply ModuleLaw.Hom.ext
    apply CommLaw.Hom.ext
    rw [transition_coordinates, X.transition_self]
    rfl
  transition_cocycle A a b c ha hb hc := by
    apply Iso.ext_hom
    apply ModuleLaw.Hom.ext
    apply CommLaw.Hom.ext
    change (q.transition A b c hb hc).hom.toHom.toCoordinateMap.comp
      (q.transition A a b ha hb).hom.toHom.toCoordinateMap =
        (q.transition A a c ha hc).hom.toHom.toCoordinateMap
    rw [transition_coordinates, transition_coordinates, transition_coordinates]
    exact congrArg (fun f => f.hom.toHom.toCoordinateMap)
      (X.transition_cocycle A (q.source a) (q.source b) (q.source c)
        (q.source_unit A a ha) (q.source_unit A b hb) (q.source_unit A c hc))
  transition_natural φ a b ha hb ha' hb' := by
    rw [transition_coordinates, transition_coordinates]
    exact X.transition_natural φ (q.source a) (q.source b)
      (q.source_unit _ a ha) (q.source_unit _ b hb)
      (q.source_unit _ a ha') (q.source_unit _ b hb')

/-- Evaluation of the chart identification preserves each actual tuple. -/
def chartEquiv (A : CommAlgCat.{v} R) (b : q.opens)
    (hb : IsUnit (algebraMap R A b.val)) :
    q.atlas.ChartPoint A b hb ≃ₗ[O] X.ChartPoint A (q.source b) (q.source_unit A b hb) :=
  (q.chartIso A b hb).onPoints

@[simp]
theorem chartEquiv_apply (A : CommAlgCat.{v} R) (b : q.opens)
    (hb : IsUnit (algebraMap R A b.val)) (x : q.atlas.ChartPoint A b hb) :
    q.chartEquiv A b hb x = x := by
  change SeriesPoint.eval CoordinateMap.id x = x
  exact SeriesPoint.eval_id x

@[simp]
theorem chartEquiv_symm_apply (A : CommAlgCat.{v} R) (b : q.opens)
    (hb : IsUnit (algebraMap R A b.val))
    (x : X.ChartPoint A (q.source b) (q.source_unit A b hb)) :
    (q.chartEquiv A b hb).symm x = x := by
  change SeriesPoint.eval CoordinateMap.id x = x
  exact SeriesPoint.eval_id x

/-- The identity tuple function with the O-linearity of the formal chart comparison. -/
def chartMap (A : CommAlgCat.{v} R) (b : q.opens)
    (hb : IsUnit (algebraMap R A b.val)) :
    X.ChartPoint A (q.source b) (q.source_unit A b hb) →ₗ[O] q.atlas.ChartPoint A b hb :=
  (q.chartEquiv A b hb).symm.toLinearMap.copy (fun x => x)
    (funext (fun x => (q.chartEquiv_symm_apply A b hb x).symm))

/-- The refined transition evaluates to the original chart transition. -/
theorem transitionPoints (A : CommAlgCat.{v} R) (a b : q.opens)
    (ha : IsUnit (algebraMap R A a.val)) (hb : IsUnit (algebraMap R A b.val))
    (x : q.atlas.ChartPoint A a ha) :
    q.atlas.transitionPoints A a b ha hb x =
      X.transitionPoints A (q.source a) (q.source b) (q.source_unit A a ha)
        (q.source_unit A b hb) x := by
  change SeriesPoint.eval (q.transition A a b ha hb).hom.toHom.toCoordinateMap x =
    SeriesPoint.eval _ x
  rw [q.transition_coordinates]

/-- View a refined chart test as a test in its chosen original chart. -/
def restrictTest {A : CommAlgCat.{v} R} (t : q.atlas.ChartTest A) : X.ChartTest A :=
  ⟨t.algebra, t.map, q.source t.chart, q.source_unit t.algebra t.chart t.isUnit⟩

/-- Restrict every actual compatible family to the finer atlas. -/
def onPoints (A : CommAlgCat.{v} R) : X.Point A →ₗ[O] q.atlas.Point A where
  toFun x := ⟨fun t => x.val (q.restrictTest t), ⟨by
    intro B C φ ψ b hb hc
    change SeriesPoint.eval CoordinateMap.id
      (SeriesPoint.map ψ.hom.toRingHom
        (x.val ⟨B, φ, q.source b, q.source_unit B b hb⟩)) =
      x.val ⟨C, φ ≫ ψ, q.source b, q.source_unit C b hc⟩
    rw [SeriesPoint.eval_id]
    have h := x.property.1 B C φ ψ (q.source b)
      (q.source_unit B b hb) (q.source_unit C b hc)
    rw [pointMap_apply] at h
    exact h,
  by
    intro B φ b c hb hc
    change q.opens at b c
    change SeriesPoint.eval (q.transition B b c hb hc).hom.toHom.toCoordinateMap
      (x.val ⟨B, φ, q.source b, q.source_unit B b hb⟩) =
      x.val ⟨B, φ, q.source c, q.source_unit B c hc⟩
    rw [q.transition_coordinates]
    exact x.property.2 B φ (q.source b) (q.source c)
      (q.source_unit B b hb) (q.source_unit B c hc)⟩⟩
  map_add' x y := by
    apply Subtype.ext
    funext t
    exact (q.chartMap t.algebra t.chart t.isUnit).map_add
      (x.val (q.restrictTest t)) (y.val (q.restrictTest t))
  map_smul' a x := by
    apply Subtype.ext
    funext t
    exact (q.chartMap t.algebra t.chart t.isUnit).map_smul a (x.val (q.restrictTest t))

@[simp]
theorem onPoints_apply (A : CommAlgCat.{v} R) (x : X.Point A)
    (t : q.atlas.ChartTest A) :
    (q.onPoints A x).val t = x.val (q.restrictTest t) := rfl

/-- Refinement restriction commutes with every coefficient-algebra map. -/
theorem onPoints_natural {A B : CommAlgCat.{v} R} (φ : A ⟶ B) (x : X.Point A) :
    q.atlas.mapPoints φ (q.onPoints A x) = q.onPoints B (X.mapPoints φ x) := by
  apply Subtype.ext
  funext t
  rfl

/-- The constructed natural restriction transformation of actual point functors. -/
def pointNatTrans : X.pointFunctor ⟶ q.atlas.pointFunctor where
  app A := ModuleCat.ofHom (q.onPoints A)
  naturality A B φ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (q.onPoints_natural φ x).symm

end CoverRefinement

end Langlands.FormalGroup.ModuleLaw.BasicAtlas
