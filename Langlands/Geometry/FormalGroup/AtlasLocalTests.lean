import Langlands.Geometry.FormalGroup.BasicAtlas

/-! # Universal localized tests for coordinate atlases -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ : Type} [Finite σ]

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable (X : BasicAtlas O R σ)

/-- The canonical coefficient algebra obtained by inverting a chart element. -/
abbrev localAlgebra (A : CommAlgCat.{v} R) (a : X.opens) : CommAlgCat.{v} R :=
  CommAlgCat.of R (Localization.Away (algebraMap R A a.val))

/-- The structural map to the localized test algebra. -/
def localizationMap (A : CommAlgCat.{v} R) (a : X.opens) : A ⟶ X.localAlgebra A a :=
  CommAlgCat.ofHom (IsScalarTower.toAlgHom R A
    (Localization.Away (algebraMap R A a.val)))

/-- The chosen chart is defined over its canonical localized test. -/
theorem localUnit (A : CommAlgCat.{v} R) (a : X.opens) :
    IsUnit (algebraMap R (X.localAlgebra A a) a.val) := by
  change IsUnit (algebraMap R (Localization.Away (algebraMap R A a.val)) a.val)
  rw [IsScalarTower.algebraMap_apply R A (Localization.Away (algebraMap R A a.val))]
  exact IsLocalization.Away.algebraMap_isUnit (algebraMap R A a.val)

/-- One universal chart test for each chart. -/
def localTest (A : CommAlgCat.{v} R) (a : X.opens) : X.ChartTest A :=
  ⟨X.localAlgebra A a, X.localizationMap A a, a, X.localUnit A a⟩

/-- The universal localization lift factors any chart test. -/
def testFactor {A : CommAlgCat.{v} R} (t : X.ChartTest A) :
    X.localAlgebra A t.chart ⟶ t.algebra :=
  CommAlgCat.ofHom (IsLocalization.Away.liftAlgHom (algebraMap R A t.chart.val)
    (f := t.map.hom) (by simpa only [AlgHom.commutes] using t.isUnit))

@[simp]
theorem localizationMap_testFactor {A : CommAlgCat.{v} R} (t : X.ChartTest A) :
    X.localizationMap A t.chart ≫ X.testFactor t = t.map := by
  ext z
  exact IsLocalization.Away.lift_eq (g := t.map.hom.toRingHom)
    (algebraMap R A t.chart.val)
    (by change IsUnit (t.map.hom (algebraMap R A t.chart.val));
        simpa only [AlgHom.commutes] using t.isUnit) z

/-- Every component of a compatible family comes from its localized test. -/
theorem component_from_localTest {A : CommAlgCat.{v} R} (x : X.Point A)
    (t : X.ChartTest A) :
    pointMap (X.chart t.chart) (X.testFactor t) (X.localUnit A t.chart) t.isUnit
      (x.val (X.localTest A t.chart)) = x.val t := by
  have h := x.property.1 (X.localAlgebra A t.chart) t.algebra
    (X.localizationMap A t.chart) (X.testFactor t) t.chart
    (X.localUnit A t.chart) t.isUnit
  exact h.trans (congrArg (β := X.ChartPoint t.algebra t.chart t.isUnit)
    (fun f : A ⟶ t.algebra =>
      (x.val ⟨t.algebra, f, t.chart, t.isUnit⟩ : X.ChartPoint t.algebra t.chart t.isUnit))
    (X.localizationMap_testFactor t))

/-- Equality of atlas points is detected on one localization per chart. -/
theorem ext_localTests {A : CommAlgCat.{v} R} {x y : X.Point A}
    (h : ∀ a : X.opens, x.val (X.localTest A a) = y.val (X.localTest A a)) : x = y := by
  apply Subtype.ext
  funext t
  rw [← X.component_from_localTest x t, ← X.component_from_localTest y t, h t.chart]

instance localChartPointAddCommGroup (A : CommAlgCat.{v} R) (a : X.opens) :
    AddCommGroup (X.ChartPoint (X.localAlgebra A a) a (X.localUnit A a)) :=
  X.chartPointAddCommGroup (X.localAlgebra A a) a (X.localUnit A a)

instance localChartPointModule (A : CommAlgCat.{v} R) (a : X.opens) :
    Module O (X.ChartPoint (X.localAlgebra A a) a (X.localUnit A a)) :=
  X.chartPointModule (X.localAlgebra A a) a (X.localUnit A a)

/-- Actual tuples at the universal localized tests. -/
def localizedCoordinates (A : CommAlgCat.{v} R) :
    X.Point A →ₗ[O] ((a : X.opens) →
      X.ChartPoint (X.localAlgebra A a) a (X.localUnit A a)) where
  toFun x a := x.val (X.localTest A a)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Canonical localized coordinates faithfully describe every atlas point. -/
theorem localizedCoordinates_injective (A : CommAlgCat.{v} R) :
    Function.Injective (X.localizedCoordinates A) := by
  intro x y h
  exact X.ext_localTests (fun a => congrFun h a)

end Langlands.FormalGroup.ModuleLaw.BasicAtlas
