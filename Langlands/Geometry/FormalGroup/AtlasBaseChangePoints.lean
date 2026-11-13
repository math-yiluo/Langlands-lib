import Langlands.Geometry.FormalGroup.AtlasBaseChange
import Langlands.Geometry.FormalGroup.CoefficientPoints

/-! # Compatible-family points and coefficient extension of formal atlases -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ : Type} [Finite σ]

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable (X : BasicAtlas O R σ) (S : CommAlgCat.{v} R)

/-- Restrict an image-cover test to the chosen original chart. -/
def restrictChartTest {A : CommAlgCat.{v} S} (t : (X.baseChange S).ChartTest A) :
    X.ChartTest (restrictTest S A) :=
  ⟨restrictTest S t.algebra, restrictTestHom S t.map, X.baseSource S t.chart,
    X.baseSource_unit S t.algebra t.chart t.isUnit⟩

/-- Evaluating the new transition agrees with the original transition. -/
theorem baseChangeTransitionPoints (A : CommAlgCat.{v} S) (a b : X.baseOpens S)
    (ha : IsUnit (algebraMap S A a.val)) (hb : IsUnit (algebraMap S A b.val))
    (x : (X.baseChange S).ChartPoint A a ha) :
    (X.baseChange S).transitionPoints A a b ha hb x =
      X.transitionPoints (restrictTest S A) (X.baseSource S a) (X.baseSource S b)
        (X.baseSource_unit S A a ha) (X.baseSource_unit S A b hb) x := by
  change SeriesPoint.eval (X.baseTransition S A a b ha hb).hom.toHom.toCoordinateMap x =
    SeriesPoint.eval _ x
  rw [X.baseTransition_coordinates]

/-- The identity tuple map with the linearity of the actual chart comparison. -/
def baseChangeChartMap (A : CommAlgCat.{v} S) (b : X.baseOpens S)
    (hb : IsUnit (algebraMap S A b.val)) :
    X.ChartPoint (restrictTest S A) (X.baseSource S b) (X.baseSource_unit S A b hb) →ₗ[O]
      (X.baseChange S).ChartPoint A b hb :=
  (X.baseChangeChartEquiv S A b hb).symm.toLinearMap.copy (fun x => x)
    (funext (fun x => (X.baseChangeChartEquiv_symm_apply S A b hb x).symm))

/-- Restricting a compatible family gives a compatible family for the new atlas. -/
def toBaseChangePoints (A : CommAlgCat.{v} S) :
    X.Point (restrictTest S A) →ₗ[O] (X.baseChange S).Point A where
  toFun x := ⟨fun t => x.val (X.restrictChartTest S t), ⟨by
    intro B C φ ψ a hb hc
    change SeriesPoint.eval CoordinateMap.id
      (SeriesPoint.map ψ.hom.toRingHom
        (x.val ⟨restrictTest S B, restrictTestHom S φ, X.baseSource S a,
          X.baseSource_unit S B a hb⟩)) =
      x.val ⟨restrictTest S C, restrictTestHom S (φ ≫ ψ), X.baseSource S a,
        X.baseSource_unit S C a hc⟩
    rw [SeriesPoint.eval_id]
    have h := x.property.1 (restrictTest S B) (restrictTest S C)
      (restrictTestHom S φ) (restrictTestHom S ψ) (X.baseSource S a)
      (X.baseSource_unit S B a hb) (X.baseSource_unit S C a hc)
    rw [pointMap_apply] at h
    change SeriesPoint.map ψ.hom.toRingHom
      (x.val ⟨restrictTest S B, restrictTestHom S φ, X.baseSource S a,
        X.baseSource_unit S B a hb⟩) =
      x.val ⟨restrictTest S C, restrictTestHom S (φ ≫ ψ), X.baseSource S a,
        X.baseSource_unit S C a hc⟩ at h
    exact h,
  by
    intro B φ a b ha hb
    change SeriesPoint.eval (X.baseTransition S B a b ha hb).hom.toHom.toCoordinateMap
      (x.val ⟨restrictTest S B, restrictTestHom S φ, X.baseSource S a,
        X.baseSource_unit S B a ha⟩) =
      x.val ⟨restrictTest S B, restrictTestHom S φ, X.baseSource S b,
        X.baseSource_unit S B b hb⟩
    rw [X.baseTransition_coordinates S B a b ha hb]
    exact x.property.2 (restrictTest S B) (restrictTestHom S φ)
      (X.baseSource S a) (X.baseSource S b)
      (X.baseSource_unit S B a ha) (X.baseSource_unit S B b hb)⟩⟩
  map_add' x y := by
    apply Subtype.ext
    funext t
    exact
      (X.baseChangeChartMap S t.algebra t.chart t.isUnit).map_add
        (x.val (X.restrictChartTest S t)) (y.val (X.restrictChartTest S t))
  map_smul' c x := by
    apply Subtype.ext
    funext t
    exact
      (X.baseChangeChartMap S t.algebra t.chart t.isUnit).map_smul c
        (x.val (X.restrictChartTest S t))

@[simp]
theorem toBaseChangePoints_apply (A : CommAlgCat.{v} S)
    (x : X.Point (restrictTest S A)) (t : (X.baseChange S).ChartTest A) :
    (X.toBaseChangePoints S A x).val t = x.val (X.restrictChartTest S t) := rfl

/-- An original generator gives its actual image generator. -/
def imageChart (a : X.opens) : X.baseOpens S :=
  ⟨algebraMap R S a.val, ⟨a.val, a.property, rfl⟩⟩

/-- Every original test acquires the coefficient action through its source. -/
def liftTestAlgebra {A : CommAlgCat.{v} S} (B : CommAlgCat.{v} R)
    (φ : restrictTest S A ⟶ B) : CommAlgCat.{v} S :=
  letI : Algebra S B :=
    (φ.hom.comp (IsScalarTower.toAlgHom R S A)).toRingHom.toAlgebra
  CommAlgCat.of S B

/-- The original coefficient map is linear for the induced S-action. -/
def liftTestMap {A : CommAlgCat.{v} S} (B : CommAlgCat.{v} R)
    (φ : restrictTest S A ⟶ B) : A ⟶ liftTestAlgebra S B φ :=
  letI : Algebra S B :=
    (φ.hom.comp (IsScalarTower.toAlgHom R S A)).toRingHom.toAlgebra
  CommAlgCat.ofHom { __ := φ.hom.toRingHom, commutes' := fun _ => rfl }

/-- The identity tuple map from the lifted test retains the original R-action. -/
def unliftTestMap {A : CommAlgCat.{v} S} (B : CommAlgCat.{v} R)
    (φ : restrictTest S A ⟶ B) :
    restrictTest S (liftTestAlgebra S B φ) ⟶ B :=
  CommAlgCat.ofHom {
    __ := RingHom.id B
    commutes' := fun r => by
      change φ.hom (algebraMap S A (algebraMap R S r)) = algebraMap R B r
      change φ.hom (algebraMap R A r) = algebraMap R B r
      exact φ.hom.commutes r }

/-- Coefficient maps between original tests respect their induced S-actions. -/
def liftTestHom {A : CommAlgCat.{v} S} {B C : CommAlgCat.{v} R}
    (φ : restrictTest S A ⟶ B) (ψ : B ⟶ C) :
    liftTestAlgebra S B φ ⟶ liftTestAlgebra S C (φ ≫ ψ) :=
  CommAlgCat.ofHom (X := liftTestAlgebra S B φ)
    (Y := liftTestAlgebra S C (φ ≫ ψ))
    { __ := ψ.hom.toRingHom, commutes' := fun _ => rfl }

/-- A lifted test has the original R-action on its actual underlying ring. -/
theorem liftTest_R {A : CommAlgCat.{v} S} (B : CommAlgCat.{v} R)
    (φ : restrictTest S A ⟶ B) (r : R) :
    algebraMap R (restrictTest S (liftTestAlgebra S B φ)) r = algebraMap R B r :=
  (unliftTestMap S B φ).hom.commutes r

/-- The image of a unit original generator is a unit in the lifted test. -/
theorem liftImage_unit {A : CommAlgCat.{v} S} (B : CommAlgCat.{v} R)
    (φ : restrictTest S A ⟶ B) (a : X.opens)
    (ha : IsUnit (algebraMap R B a.val)) :
    IsUnit (algebraMap S (liftTestAlgebra S B φ) (X.imageChart S a).val) := by
  change IsUnit (algebraMap R (restrictTest S (liftTestAlgebra S B φ)) a.val)
  rw [liftTest_R]
  exact ha

/-- The chosen preimage generator is also a unit in the original test. -/
theorem liftSource_unit {A : CommAlgCat.{v} S} (B : CommAlgCat.{v} R)
    (φ : restrictTest S A ⟶ B) (a : X.opens)
    (ha : IsUnit (algebraMap R B a.val)) :
    IsUnit (algebraMap R B (X.baseSource S (X.imageChart S a)).val) :=
  unit_map (unliftTestMap S B φ)
    (X.baseSource_unit S (liftTestAlgebra S B φ) (X.imageChart S a)
      (X.liftImage_unit S B φ a ha))

/-- Lift an original chart test using its induced coefficient action. -/
def liftChartTest {A : CommAlgCat.{v} S} (t : X.ChartTest (restrictTest S A)) :
    (X.baseChange S).ChartTest A :=
  ⟨liftTestAlgebra S t.algebra t.map, liftTestMap S t.algebra t.map,
    X.imageChart S t.chart, X.liftImage_unit S t.algebra t.map t.chart t.isUnit⟩

/-- Read an image-chart tuple on the lifted test, in its actual underlying ring. -/
def liftValue {A : CommAlgCat.{v} S} (y : (X.baseChange S).Point A)
    (B : CommAlgCat.{v} R) (φ : restrictTest S A ⟶ B) (a : X.opens)
    (ha : IsUnit (algebraMap R B a.val)) :
    X.ChartPoint B (X.baseSource S (X.imageChart S a)) (X.liftSource_unit S B φ a ha) :=
  y.val (X.liftChartTest S ⟨B, φ, a, ha⟩)

/-- Compatible families are natural on induced S-tests. -/
theorem liftValue_natural {A : CommAlgCat.{v} S} (y : (X.baseChange S).Point A)
    {B C : CommAlgCat.{v} R} (φ : restrictTest S A ⟶ B) (ψ : B ⟶ C)
    (a : X.opens) (hb : IsUnit (algebraMap R B a.val))
    (hc : IsUnit (algebraMap R C a.val)) :
    pointMap (X.chart (X.baseSource S (X.imageChart S a))) ψ
      (X.liftSource_unit S B φ a hb) (X.liftSource_unit S C (φ ≫ ψ) a hc)
      (X.liftValue S y B φ a hb) =
      X.liftValue S y C (φ ≫ ψ) a hc := by
  rw [pointMap_apply]
  have h := y.property.1 (liftTestAlgebra S B φ) (liftTestAlgebra S C (φ ≫ ψ))
    (liftTestMap S B φ) (liftTestHom S φ ψ) (X.imageChart S a)
    (X.liftImage_unit S B φ a hb) (X.liftImage_unit S C (φ ≫ ψ) a hc)
  rw [pointMap_apply] at h
  change SeriesPoint.map ψ.hom.toRingHom (X.liftValue S y B φ a hb) =
    X.liftValue S y C (φ ≫ ψ) a hc at h
  exact h

/-- Restriction of the lifted test changes no actual transition series. -/
theorem liftTest_transition {A : CommAlgCat.{v} S} (B : CommAlgCat.{v} R)
    (φ : restrictTest S A ⟶ B) (a b : X.opens)
    (ha : IsUnit (algebraMap R (restrictTest S (liftTestAlgebra S B φ)) a.val))
    (hb : IsUnit (algebraMap R (restrictTest S (liftTestAlgebra S B φ)) b.val))
    (ha' : IsUnit (algebraMap R B a.val)) (hb' : IsUnit (algebraMap R B b.val)) :
    (X.transition (restrictTest S (liftTestAlgebra S B φ)) a b ha hb).hom.toHom.toCoordinateMap =
      (X.transition B a b ha' hb').hom.toHom.toCoordinateMap := by
  have h := X.transition_natural (unliftTestMap S B φ) a b ha hb ha' hb'
  change ((X.transition (restrictTest S (liftTestAlgebra S B φ)) a b ha hb).hom.toHom.toCoordinateMap.map
    (RingHom.id B)) = _ at h
  exact (CoordinateMap.map_ringHom_id
    ((X.transition (restrictTest S (liftTestAlgebra S B φ)) a b ha hb).hom.toHom.toCoordinateMap :
      CoordinateMap B σ σ)).symm.trans h

/-- Original transitions compare the lifted image-chart values. -/
theorem liftValue_transition {A : CommAlgCat.{v} S} (y : (X.baseChange S).Point A)
    (B : CommAlgCat.{v} R) (φ : restrictTest S A ⟶ B) (a b : X.opens)
    (ha : IsUnit (algebraMap R B a.val)) (hb : IsUnit (algebraMap R B b.val)) :
    X.transitionPoints B (X.baseSource S (X.imageChart S a))
      (X.baseSource S (X.imageChart S b))
      (X.liftSource_unit S B φ a ha) (X.liftSource_unit S B φ b hb)
      (X.liftValue S y B φ a ha) = X.liftValue S y B φ b hb := by
  have h := y.property.2 (liftTestAlgebra S B φ) (liftTestMap S B φ)
    (X.imageChart S a) (X.imageChart S b)
    (X.liftImage_unit S B φ a ha) (X.liftImage_unit S B φ b hb)
  rw [X.baseChangeTransitionPoints] at h
  change SeriesPoint.eval
    (X.transition (restrictTest S (liftTestAlgebra S B φ))
      (X.baseSource S (X.imageChart S a)) (X.baseSource S (X.imageChart S b)) _ _).hom.toHom.toCoordinateMap
    (X.liftValue S y B φ a ha) = X.liftValue S y B φ b hb at h
  rw [X.liftTest_transition S B φ _ _ _ _ (X.liftSource_unit S B φ a ha)
    (X.liftSource_unit S B φ b hb)] at h
  exact h

/-- Recover original-chart tuples by the original formal transition maps. -/
def fromBaseChangeFamily {A : CommAlgCat.{v} S} (y : (X.baseChange S).Point A) :
    X.Family (restrictTest S A) :=
  fun t => X.transitionPoints t.algebra (X.baseSource S (X.imageChart S t.chart)) t.chart
    (X.liftSource_unit S t.algebra t.map t.chart t.isUnit) t.isUnit
    (X.liftValue S y t.algebra t.map t.chart t.isUnit)

/-- The recovered family satisfies both actual atlas compatibility equations. -/
theorem fromBaseChangeFamily_compatible {A : CommAlgCat.{v} S}
    (y : (X.baseChange S).Point A) : X.Compatible (X.fromBaseChangeFamily S y) := by
  constructor
  · intro B C φ ψ a hb hc
    change pointMap (X.chart a) ψ hb hc
      (X.transitionPoints B (X.baseSource S (X.imageChart S a)) a _ hb
        (X.liftValue S y B φ a hb)) =
      X.transitionPoints C (X.baseSource S (X.imageChart S a)) a _ hc
        (X.liftValue S y C (φ ≫ ψ) a hc)
    rw [X.transitionPoints_natural ψ _ a _ hb
      (X.liftSource_unit S C (φ ≫ ψ) a hc) hc,
      X.liftValue_natural S y φ ψ a hb hc]
  · intro B φ a b ha hb
    change X.transitionPoints B a b ha hb
      (X.transitionPoints B (X.baseSource S (X.imageChart S a)) a _ ha
        (X.liftValue S y B φ a ha)) =
      X.transitionPoints B (X.baseSource S (X.imageChart S b)) b _ hb
        (X.liftValue S y B φ b hb)
    rw [X.transitionPoints_cocycle]
    rw [← X.liftValue_transition S y B φ a b ha hb, X.transitionPoints_cocycle]

/-- The constructed inverse on full compatible families. -/
def fromBaseChangePoints (A : CommAlgCat.{v} S) (y : (X.baseChange S).Point A) :
    X.Point (restrictTest S A) :=
  ⟨X.fromBaseChangeFamily S y, X.fromBaseChangeFamily_compatible S y⟩

/-- Restriction and lifting recover the original family component. -/
theorem toBaseChangePoints_liftValue {A : CommAlgCat.{v} S}
    (x : X.Point (restrictTest S A)) (B : CommAlgCat.{v} R)
    (φ : restrictTest S A ⟶ B) (a : X.opens) (ha : IsUnit (algebraMap R B a.val)) :
    X.liftValue S (X.toBaseChangePoints S A x) B φ a ha =
      x.val ⟨B, φ, X.baseSource S (X.imageChart S a), X.liftSource_unit S B φ a ha⟩ := by
  have h := x.property.1 (restrictTest S (liftTestAlgebra S B φ)) B
    (restrictTestHom S (liftTestMap S B φ)) (unliftTestMap S B φ)
    (X.baseSource S (X.imageChart S a))
    (X.baseSource_unit S (liftTestAlgebra S B φ) (X.imageChart S a)
      (X.liftImage_unit S B φ a ha)) (X.liftSource_unit S B φ a ha)
  rw [pointMap_apply] at h
  change SeriesPoint.map (RingHom.id B)
    (X.liftValue S (X.toBaseChangePoints S A x) B φ a ha) =
      x.val ⟨B, φ, X.baseSource S (X.imageChart S a), X.liftSource_unit S B φ a ha⟩ at h
  exact (SeriesPoint.map_id
    (X.liftValue S (X.toBaseChangePoints S A x) B φ a ha)).symm.trans h

/-- The inverse after restriction recovers every original chart test. -/
@[simp]
theorem from_toBaseChangePoints (A : CommAlgCat.{v} S)
    (x : X.Point (restrictTest S A)) :
    X.fromBaseChangePoints S A (X.toBaseChangePoints S A x) = x := by
  apply Subtype.ext
  funext t
  change X.transitionPoints t.algebra (X.baseSource S (X.imageChart S t.chart)) t.chart
    (X.liftSource_unit S t.algebra t.map t.chart t.isUnit) t.isUnit
    (X.liftValue S (X.toBaseChangePoints S A x) t.algebra t.map t.chart t.isUnit) = x.val t
  rw [X.toBaseChangePoints_liftValue]
  exact x.property.2 t.algebra t.map (X.baseSource S (X.imageChart S t.chart)) t.chart
    (X.liftSource_unit S t.algebra t.map t.chart t.isUnit) t.isUnit

/-- The induced S-action on an already supplied S-test maps identically to it. -/
def liftRestrictionHom {A B : CommAlgCat.{v} S} (φ : A ⟶ B) :
    liftTestAlgebra S (restrictTest S B) (restrictTestHom S φ) ⟶ B :=
  CommAlgCat.ofHom
    (X := liftTestAlgebra S (restrictTest S B) (restrictTestHom S φ)) (Y := B)
    { __ := RingHom.id B
      commutes' := fun s => by
        change φ.hom (algebraMap S A s) = algebraMap S B s
        exact φ.hom.commutes s }

/-- An original unit generator has a unit image in an existing S-test. -/
theorem imageChart_unit (B : CommAlgCat.{v} S) (a : X.opens)
    (ha : IsUnit (algebraMap R (restrictTest S B) a.val)) :
    IsUnit (algebraMap S B (X.imageChart S a).val) :=
  ha

/-- Lifting a restricted S-test recovers its original family value. -/
theorem liftValue_restrict {A B : CommAlgCat.{v} S} (y : (X.baseChange S).Point A)
    (φ : A ⟶ B) (a : X.opens)
    (ha : IsUnit (algebraMap R (restrictTest S B) a.val)) :
    (X.liftValue S y (restrictTest S B) (restrictTestHom S φ) a ha : SeriesPoint B σ Empty) =
      y.val ⟨B, φ, X.imageChart S a, X.imageChart_unit S B a ha⟩ := by
  have h := y.property.1
    (liftTestAlgebra S (restrictTest S B) (restrictTestHom S φ)) B
    (liftTestMap S (restrictTest S B) (restrictTestHom S φ))
    (liftRestrictionHom S φ) (X.imageChart S a)
    (X.liftImage_unit S (restrictTest S B) (restrictTestHom S φ) a ha)
    (X.imageChart_unit S B a ha)
  rw [pointMap_apply] at h
  change SeriesPoint.map (RingHom.id B)
    (X.liftValue S y (restrictTest S B) (restrictTestHom S φ) a ha) =
      y.val ⟨B, φ, X.imageChart S a, X.imageChart_unit S B a ha⟩ at h
  exact (SeriesPoint.map_id
    (X.liftValue S y (restrictTest S B) (restrictTestHom S φ) a ha :
      SeriesPoint B σ Empty)).symm.trans h

/-- The chosen original chart maps back to the given image chart. -/
@[simp]
theorem imageChart_baseSource (b : X.baseOpens S) :
    X.imageChart S (X.baseSource S b) = b :=
  Subtype.ext (X.baseSource_image S b)

/-- Equal image chart indices give the same actual tuple. -/
theorem baseFamily_chart_congr {A : CommAlgCat.{v} S} (y : (X.baseChange S).Point A)
    (B : CommAlgCat.{v} S) (φ : A ⟶ B) (a b : X.baseOpens S)
    (ha : IsUnit (algebraMap S B a.val)) (hb : IsUnit (algebraMap S B b.val))
    (h : a = b) :
    (y.val ⟨B, φ, a, ha⟩ : SeriesPoint B σ Empty) = y.val ⟨B, φ, b, hb⟩ := by
  cases h
  rfl

/-- A transition between equal original chart indices fixes its actual tuple. -/
theorem transitionPoints_of_eq (B : CommAlgCat.{v} R) (a b : X.opens)
    (ha : IsUnit (algebraMap R B a.val)) (hb : IsUnit (algebraMap R B b.val))
    (h : a = b) (x : X.ChartPoint B a ha) :
    (X.transitionPoints B a b ha hb x : SeriesPoint B σ Empty) = x := by
  cases h
  exact X.transitionPoints_self B a ha x

/-- Restriction after the inverse recovers each given image-chart component. -/
theorem to_fromBaseChangePoints_component (A : CommAlgCat.{v} S)
    (y : (X.baseChange S).Point A) (B : CommAlgCat.{v} S) (φ : A ⟶ B)
    (b : X.baseOpens S) (hb : IsUnit (algebraMap S B b.val)) :
    (X.toBaseChangePoints S A (X.fromBaseChangePoints S A y)).val ⟨B, φ, b, hb⟩ =
      y.val ⟨B, φ, b, hb⟩ := by
  change X.transitionPoints (restrictTest S B)
    (X.baseSource S (X.imageChart S (X.baseSource S b))) (X.baseSource S b)
    _ (X.baseSource_unit S B b hb)
    (X.liftValue S y (restrictTest S B) (restrictTestHom S φ) (X.baseSource S b)
      (X.baseSource_unit S B b hb)) = _
  exact (X.transitionPoints_of_eq (restrictTest S B)
    (X.baseSource S (X.imageChart S (X.baseSource S b))) (X.baseSource S b)
    _ (X.baseSource_unit S B b hb)
    (congrArg (X.baseSource S) (X.imageChart_baseSource S b)) _).trans
    ((X.liftValue_restrict S y φ (X.baseSource S b) (X.baseSource_unit S B b hb)).trans
      (X.baseFamily_chart_congr S y B φ _ b _ hb (X.imageChart_baseSource S b)))

/-- Restriction after the inverse recovers the entire image-cover family. -/
@[simp]
theorem to_fromBaseChangePoints (A : CommAlgCat.{v} S) (y : (X.baseChange S).Point A) :
    X.toBaseChangePoints S A (X.fromBaseChangePoints S A y) = y := by
  apply Subtype.ext
  funext t
  exact X.to_fromBaseChangePoints_component S A y t.algebra t.map t.chart t.isUnit

/-- Full compatible-family points agree after arbitrary coefficient extension. -/
def baseChangePointEquiv (A : CommAlgCat.{v} S) :
    X.Point (restrictTest S A) ≃ₗ[O] (X.baseChange S).Point A :=
  { X.toBaseChangePoints S A with
    invFun := X.fromBaseChangePoints S A
    left_inv := X.from_toBaseChangePoints S A
    right_inv := X.to_fromBaseChangePoints S A }

/-- The forward equivalence restricts the actual chart tests. -/
@[simp]
theorem baseChangePointEquiv_apply (A : CommAlgCat.{v} S)
    (x : X.Point (restrictTest S A)) (t : (X.baseChange S).ChartTest A) :
    (X.baseChangePointEquiv S A x).val t = x.val (X.restrictChartTest S t) := rfl

/-- The inverse equivalence uses the constructed lifted-test family. -/
@[simp]
theorem baseChangePointEquiv_symm_apply (A : CommAlgCat.{v} S)
    (y : (X.baseChange S).Point A) :
    (X.baseChangePointEquiv S A).symm y = X.fromBaseChangePoints S A y := rfl

/-- The full family comparison commutes with every S-algebra map. -/
theorem toBaseChangePoints_natural {A B : CommAlgCat.{v} S} (φ : A ⟶ B)
    (x : X.Point (restrictTest S A)) :
    (X.baseChange S).mapPoints φ (X.toBaseChangePoints S A x) =
      X.toBaseChangePoints S B (X.mapPoints (restrictTestHom S φ) x) := by
  apply Subtype.ext
  funext t
  rfl

/-- A natural isomorphism of the full actual compatible-family point functors. -/
def baseChangePointFunctorIso :
    restrictCoefficientFunctor (IsScalarTower.toAlgHom O R S) ⋙ X.pointFunctor ≅
      (X.baseChange S).pointFunctor :=
  NatIso.ofComponents
    (fun A => (X.baseChangePointEquiv S A).toModuleIso)
    (by
      intro A B φ
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact (X.toBaseChangePoints_natural S φ x).symm)

/-- The same full-family comparison on coefficient tests in which pi is nilpotent. -/
def baseChangeNilpPointFunctorIso (π : R) :
    Nilp.forget S (algebraMap R S π) ⋙
        (restrictCoefficientFunctor (IsScalarTower.toAlgHom O R S) ⋙ X.pointFunctor) ≅
      (X.baseChange S).nilpPointFunctor (algebraMap R S π) :=
  Functor.isoWhiskerLeft (Nilp.forget S (algebraMap R S π)) (X.baseChangePointFunctorIso S)

end Langlands.FormalGroup.ModuleLaw.BasicAtlas
