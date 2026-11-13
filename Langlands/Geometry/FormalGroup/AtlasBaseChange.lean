import Langlands.Geometry.FormalGroup.BasicAtlas

/-! # Coefficient extension of actual formal coordinate atlases -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ : Type} [Finite σ]

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable (X : BasicAtlas O R σ) (S : CommAlgCat.{v} R)

/-- View an S-algebra as an R-algebra through the structural map. -/
abbrev restrictTest (A : CommAlgCat.{v} S) : CommAlgCat.{v} R :=
  CommAlgCat.of R A

/-- The same coefficient homomorphism after restricting scalars. -/
def restrictTestHom {A B : CommAlgCat.{v} S} (φ : A ⟶ B) :
    restrictTest S A ⟶ restrictTest S B :=
  CommAlgCat.ofHom (φ.hom.restrictScalars R)

/-- The image principal-open generators after extending the base. -/
abbrev baseOpens : Set S := algebraMap R S '' X.opens

/-- Choose an original generator above each image generator. -/
def baseSource (b : X.baseOpens S) : X.opens :=
  ⟨Classical.choose b.property, (Classical.choose_spec b.property).1⟩

theorem baseSource_image (b : X.baseOpens S) :
    algebraMap R S (X.baseSource S b).val = b.val :=
  (Classical.choose_spec b.property).2

/-- The image generators still cover the whole affine base. -/
theorem baseOpens_covers : Ideal.span (X.baseOpens S) = ⊤ := by
  rw [baseOpens, ← Ideal.map_span, X.covers, Ideal.map_top]

/-- A unit image generator makes the chosen original generator invertible. -/
theorem baseSource_unit (A : CommAlgCat.{v} S) (b : X.baseOpens S)
    (hb : IsUnit (algebraMap S A b.val)) :
    IsUnit (algebraMap R (restrictTest S A) (X.baseSource S b).val) := by
  change IsUnit (algebraMap S A (algebraMap R S (X.baseSource S b).val))
  rw [X.baseSource_image]
  exact hb

/-- The original generator is invertible in the image localization. -/
theorem baseChartCoefficient_unit (b : X.baseOpens S) :
    IsUnit ((IsScalarTower.toAlgHom O R (Localization.Away b.val))
      (X.baseSource S b).val) := by
  change IsUnit (algebraMap R (Localization.Away b.val) (X.baseSource S b).val)
  rw [IsScalarTower.algebraMap_apply R S (Localization.Away b.val),
    X.baseSource_image]
  exact IsLocalization.Away.algebraMap_isUnit b.val

/-- The actual coefficient extension between the original and image localizations. -/
def baseChartCoefficient (b : X.baseOpens S) :
    Localization.Away (X.baseSource S b).val →ₐ[O] Localization.Away b.val :=
  IsLocalization.Away.liftAlgHom (X.baseSource S b).val
    (f := IsScalarTower.toAlgHom O R (Localization.Away b.val))
    (X.baseChartCoefficient_unit S b)

@[simp]
theorem baseChartCoefficient_algebraMap (b : X.baseOpens S) (r : R) :
    X.baseChartCoefficient S b
      (algebraMap R (Localization.Away (X.baseSource S b).val) r) =
        algebraMap R (Localization.Away b.val) r :=
  IsLocalization.Away.lift_eq (X.baseSource S b).val
    (X.baseChartCoefficient_unit S b) r

/-- The two coefficient routes from the original chart into a test agree. -/
theorem baseCoefficient_comp (A : CommAlgCat.{v} S) (b : X.baseOpens S)
    (hb : IsUnit (algebraMap S A b.val)) :
    (coefficientLift (O := O) b.val A hb).toRingHom.comp
        (X.baseChartCoefficient S b).toRingHom =
      (coefficientLift (O := O) (X.baseSource S b).val (restrictTest S A)
        (X.baseSource_unit S A b hb)).toRingHom := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (X.baseSource S b).val)
  ext r
  change coefficientLift (O := O) b.val A hb
    (X.baseChartCoefficient S b
      (algebraMap R (Localization.Away (X.baseSource S b).val) r)) =
    coefficientLift (O := O) (X.baseSource S b).val (restrictTest S A)
      (X.baseSource_unit S A b hb)
        (algebraMap R (Localization.Away (X.baseSource S b).val) r)
  rw [baseChartCoefficient_algebraMap, coefficientLift_algebraMap,
    IsScalarTower.algebraMap_apply R S (Localization.Away b.val),
    coefficientLift_algebraMap]
  rfl

/-- Extend the actual original chart law to the image localization. -/
def baseChart (b : X.baseOpens S) : ModuleLaw O (Localization.Away b.val) σ :=
  (X.chart (X.baseSource S b)).map (X.baseChartCoefficient S b)

/-- Compare the extended chart on a test with the original chart on that test. -/
def baseChartIso (A : CommAlgCat.{v} S) (b : X.baseOpens S)
    (hb : IsUnit (algebraMap S A b.val)) :
    Iso ((X.baseChart S b).map (coefficientLift (O := O) b.val A hb))
      ((X.chart (X.baseSource S b)).map
        (coefficientLift (O := O) (X.baseSource S b).val (restrictTest S A)
          (X.baseSource_unit S A b hb))) :=
  Iso.ofIdenticalCoordinates
    (by
      change ((X.chart (X.baseSource S b)).groupLaw.addition.map
        (X.baseChartCoefficient S b).toRingHom).map
        (coefficientLift (O := O) b.val A hb).toRingHom = _
      rw [CoordinateMap.map_ringHom_comp, X.baseCoefficient_comp]
      rfl)
    (fun a => by
      change (((X.chart (X.baseSource S b)).action a).toCoordinateMap.map
        (X.baseChartCoefficient S b).toRingHom).map
        (coefficientLift (O := O) b.val A hb).toRingHom = _
      rw [CoordinateMap.map_ringHom_comp, X.baseCoefficient_comp]
      rfl)

/-- Conjugate the actual original transition by the chart comparisons. -/
def baseTransition (A : CommAlgCat.{v} S) (a b : X.baseOpens S)
    (ha : IsUnit (algebraMap S A a.val)) (hb : IsUnit (algebraMap S A b.val)) :
    Iso ((X.baseChart S a).map (coefficientLift (O := O) a.val A ha))
      ((X.baseChart S b).map (coefficientLift (O := O) b.val A hb)) :=
  (X.baseChartIso S A a ha).trans
    ((X.transition (restrictTest S A) (X.baseSource S a) (X.baseSource S b)
      (X.baseSource_unit S A a ha) (X.baseSource_unit S A b hb)).trans
        (X.baseChartIso S A b hb).symm)

/-- The new transition has exactly the original transition's coordinate series. -/
@[simp]
theorem baseTransition_coordinates (A : CommAlgCat.{v} S) (a b : X.baseOpens S)
    (ha : IsUnit (algebraMap S A a.val)) (hb : IsUnit (algebraMap S A b.val)) :
    (X.baseTransition S A a b ha hb).hom.toHom.toCoordinateMap =
      (X.transition (restrictTest S A) (X.baseSource S a) (X.baseSource S b)
        (X.baseSource_unit S A a ha) (X.baseSource_unit S A b hb)).hom.toHom.toCoordinateMap := by
  change (CoordinateMap.id.comp
    (X.transition (restrictTest S A) (X.baseSource S a) (X.baseSource S b)
      (X.baseSource_unit S A a ha) (X.baseSource_unit S A b hb)).hom.toHom.toCoordinateMap).comp
        CoordinateMap.id = _
  rw [CoordinateMap.id_comp, CoordinateMap.comp_id]

/-- Coefficient extension of an actual formal module atlas. -/
def baseChange : BasicAtlas O S σ where
  opens := X.baseOpens S
  covers := X.baseOpens_covers S
  chart := X.baseChart S
  transition := X.baseTransition S
  transition_self A a ha := by
    apply Iso.ext_hom
    apply ModuleLaw.Hom.ext
    apply CommLaw.Hom.ext
    rw [baseTransition_coordinates, X.transition_self]
    rfl
  transition_cocycle A a b c ha hb hc := by
    apply Iso.ext_hom
    apply ModuleLaw.Hom.ext
    apply CommLaw.Hom.ext
    change (X.baseTransition S A b c hb hc).hom.toHom.toCoordinateMap.comp
      (X.baseTransition S A a b ha hb).hom.toHom.toCoordinateMap =
        (X.baseTransition S A a c ha hc).hom.toHom.toCoordinateMap
    rw [baseTransition_coordinates, baseTransition_coordinates, baseTransition_coordinates]
    exact congrArg (fun f => f.hom.toHom.toCoordinateMap)
      (X.transition_cocycle (restrictTest S A)
        (X.baseSource S a) (X.baseSource S b) (X.baseSource S c)
          (X.baseSource_unit S A a ha) (X.baseSource_unit S A b hb)
            (X.baseSource_unit S A c hc))
  transition_natural φ a b ha hb ha' hb' := by
    rw [baseTransition_coordinates, baseTransition_coordinates]
    exact X.transition_natural (restrictTestHom S φ)
      (X.baseSource S a) (X.baseSource S b)
      (X.baseSource_unit S _ a ha) (X.baseSource_unit S _ b hb)
      (X.baseSource_unit S _ a ha') (X.baseSource_unit S _ b hb')

/-- Evaluation compares the new chart points with the chosen original chart. -/
def baseChangeChartEquiv (A : CommAlgCat.{v} S) (b : X.baseOpens S)
    (hb : IsUnit (algebraMap S A b.val)) :
    (X.baseChange S).ChartPoint A b hb ≃ₗ[O]
      X.ChartPoint (restrictTest S A) (X.baseSource S b)
        (X.baseSource_unit S A b hb) :=
  (X.baseChartIso S A b hb).onPoints

/-- The chart comparison preserves the actual nilpotent coordinate tuple. -/
@[simp]
theorem baseChangeChartEquiv_apply (A : CommAlgCat.{v} S) (b : X.baseOpens S)
    (hb : IsUnit (algebraMap S A b.val))
    (x : (X.baseChange S).ChartPoint A b hb) :
    X.baseChangeChartEquiv S A b hb x = x := by
  change SeriesPoint.eval CoordinateMap.id x = x
  exact SeriesPoint.eval_id x

/-- The inverse chart comparison also preserves the coordinate tuple. -/
@[simp]
theorem baseChangeChartEquiv_symm_apply (A : CommAlgCat.{v} S) (b : X.baseOpens S)
    (hb : IsUnit (algebraMap S A b.val))
    (x : X.ChartPoint (restrictTest S A) (X.baseSource S b)
      (X.baseSource_unit S A b hb)) :
    (X.baseChangeChartEquiv S A b hb).symm x = x := by
  change SeriesPoint.eval CoordinateMap.id x = x
  exact SeriesPoint.eval_id x

end Langlands.FormalGroup.ModuleLaw.BasicAtlas
