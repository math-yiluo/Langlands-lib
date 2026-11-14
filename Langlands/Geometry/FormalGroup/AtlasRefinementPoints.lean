import Langlands.Geometry.FormalGroup.AtlasRefinement
import Langlands.Geometry.FormalGroup.AtlasBaseChange
import Langlands.Geometry.FormalGroup.AtlasLocalTests
import Langlands.Geometry.FormalGroup.ZariskiPointDescent

/-! # Actual point descent for refinements of varying-law atlases -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas.CoverRefinement

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ : Type} [Finite σ]

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {X : BasicAtlas O R σ} (q : CoverRefinement X)

/-- Express a finer-chart component in any original chart available over the test. -/
def transportedValue {A : CommAlgCat.{v} R} (y : q.atlas.Point A)
    (B : CommAlgCat.{v} R) (φ : A ⟶ B) (a : X.opens)
    (ha : IsUnit (algebraMap R B a.val)) (b : q.opens)
    (hb : IsUnit (algebraMap R B b.val)) : X.ChartPoint B a ha :=
  X.transitionPoints B (q.source b) a (q.source_unit B b hb) ha
    (y.val ⟨B, φ, b, hb⟩)

/-- Transport of finer components is natural under actual coefficient maps. -/
theorem transportedValue_natural {A B C : CommAlgCat.{v} R} (y : q.atlas.Point A)
    (φ : A ⟶ B) (ψ : B ⟶ C) (a : X.opens)
    (ha : IsUnit (algebraMap R B a.val)) (ha' : IsUnit (algebraMap R C a.val))
    (b : q.opens) (hb : IsUnit (algebraMap R B b.val))
    (hb' : IsUnit (algebraMap R C b.val)) :
    pointMap (X.chart a) ψ ha ha' (q.transportedValue y B φ a ha b hb) =
      q.transportedValue y C (φ ≫ ψ) a ha' b hb' := by
  let z : X.ChartPoint B (q.source b) (q.source_unit B b hb) :=
    y.val ⟨B, φ, b, hb⟩
  have h : SeriesPoint.map ψ.hom.toRingHom z = y.val ⟨C, φ ≫ ψ, b, hb'⟩ :=
    (pointMap_apply (q.atlas.chart b) ψ hb hb' _).symm.trans
      (y.property.1 B C φ ψ b hb hb')
  have hz : pointMap (X.chart (q.source b)) ψ (q.source_unit B b hb)
      (q.source_unit C b hb') z = y.val ⟨C, φ ≫ ψ, b, hb'⟩ :=
    (pointMap_apply (X.chart (q.source b)) ψ _ _ z).trans h
  exact (X.transitionPoints_natural ψ (q.source b) a
    (q.source_unit B b hb) ha (q.source_unit C b hb') ha' z).trans
      (congrArg (X.transitionPoints C (q.source b) a (q.source_unit C b hb') ha') hz)

/-- Overlap compatibility makes the transported tuple independent of the finer chart. -/
theorem transportedValue_independent {A : CommAlgCat.{v} R} (y : q.atlas.Point A)
    (B : CommAlgCat.{v} R) (φ : A ⟶ B) (a : X.opens)
    (ha : IsUnit (algebraMap R B a.val)) (b c : q.opens)
    (hb : IsUnit (algebraMap R B b.val)) (hc : IsUnit (algebraMap R B c.val)) :
    q.transportedValue y B φ a ha b hb = q.transportedValue y B φ a ha c hc := by
  let z : X.ChartPoint B (q.source b) (q.source_unit B b hb) :=
    y.val ⟨B, φ, b, hb⟩
  have h : X.transitionPoints B (q.source b) (q.source c)
      (q.source_unit B b hb) (q.source_unit B c hc) z = y.val ⟨B, φ, c, hc⟩ :=
    (q.transitionPoints B b c hb hc _).symm.trans (y.property.2 B φ b c hb hc)
  exact (X.transitionPoints_cocycle B (q.source b) (q.source c) a
    (q.source_unit B b hb) (q.source_unit B c hc) ha z).symm.trans
      (congrArg (X.transitionPoints B (q.source c) a (q.source_unit B c hc) ha) h)

/-- Transported tuples obey every original chart transition. -/
theorem transportedValue_transition {A : CommAlgCat.{v} R} (y : q.atlas.Point A)
    (B : CommAlgCat.{v} R) (φ : A ⟶ B) (a a' : X.opens)
    (ha : IsUnit (algebraMap R B a.val)) (ha' : IsUnit (algebraMap R B a'.val))
    (b : q.opens) (hb : IsUnit (algebraMap R B b.val)) :
    X.transitionPoints B a a' ha ha' (q.transportedValue y B φ a ha b hb) =
      q.transportedValue y B φ a' ha' b hb :=
  X.transitionPoints_cocycle B (q.source b) a a' (q.source_unit B b hb) ha ha' _

/-- The coefficient-naturality equation on the underlying tuples. -/
theorem transportedValue_map {A B C : CommAlgCat.{v} R} (y : q.atlas.Point A)
    (φ : A ⟶ B) (ψ : B ⟶ C) (a : X.opens)
    (ha : IsUnit (algebraMap R B a.val)) (ha' : IsUnit (algebraMap R C a.val))
    (b : q.opens) (hb : IsUnit (algebraMap R B b.val))
    (hb' : IsUnit (algebraMap R C b.val)) :
    SeriesPoint.map ψ.hom.toRingHom (q.transportedValue y B φ a ha b hb) =
      q.transportedValue y C (φ ≫ ψ) a ha' b hb' :=
  (pointMap_apply (X.chart a) ψ ha ha' _).symm.trans
    (q.transportedValue_natural y φ ψ a ha ha' b hb hb')

/-- The finer-chart test over one generator of the image cover of a test algebra. -/
def imageTest (B : CommAlgCat.{v} R) (c : q.atlas.baseOpens B) : q.atlas.ChartTest B :=
  ⟨CommAlgCat.of R (Localization.Away c.val),
    CommAlgCat.ofHom (IsScalarTower.toAlgHom R B (Localization.Away c.val)),
    q.atlas.baseSource B c, q.atlas.baseChartCoefficient_unit B c⟩

/-- Local finer tuples, all expressed in the fixed original chart of a test. -/
def localFamily {A : CommAlgCat.{v} R} (y : q.atlas.Point A) (t : X.ChartTest A) :
    (c : q.atlas.baseOpens t.algebra) → SeriesPoint (Localization.Away c.val) σ Empty :=
  fun c => q.transportedValue y (q.imageTest t.algebra c).algebra
    (t.map ≫ (q.imageTest t.algebra c).map) t.chart
    (unit_map (q.imageTest t.algebra c).map t.isUnit)
    (q.imageTest t.algebra c).chart (q.imageTest t.algebra c).isUnit

/-- Fixed-chart local tuples match on every actual localized overlap. -/
theorem localFamily_compatible {A : CommAlgCat.{v} R} (y : q.atlas.Point A)
    (t : X.ChartTest A) :
    SeriesPoint.BasicCompatible (q.atlas.baseOpens t.algebra) (q.localFamily y t) := by
  intro b c
  let B : CommAlgCat.{v} R :=
    CommAlgCat.of R (Localization.Away (b.val * c.val))
  let φ : t.algebra ⟶ B := CommAlgCat.ofHom (IsScalarTower.toAlgHom R t.algebra B)
  let ψb : (q.imageTest t.algebra b).algebra ⟶ B :=
    CommAlgCat.ofHom {
      __ := IsLocalization.Away.awayToAwayRight
        (S := Localization.Away b.val) (P := Localization.Away (b.val * c.val)) b.val c.val
      commutes' r := by
        change IsLocalization.Away.awayToAwayRight b.val c.val
          (algebraMap t.algebra (Localization.Away b.val) (algebraMap R t.algebra r)) =
            algebraMap t.algebra (Localization.Away (b.val * c.val)) (algebraMap R t.algebra r)
        exact IsLocalization.Away.awayToAwayRight_eq b.val c.val _ }
  let ψc : (q.imageTest t.algebra c).algebra ⟶ B :=
    CommAlgCat.ofHom {
      __ := IsLocalization.Away.awayToAwayLeft
        (S := Localization.Away c.val) (P := Localization.Away (b.val * c.val)) c.val b.val
      commutes' r := by
        change IsLocalization.Away.awayToAwayLeft c.val b.val
          (algebraMap t.algebra (Localization.Away c.val) (algebraMap R t.algebra r)) =
            algebraMap t.algebra (Localization.Away (b.val * c.val)) (algebraMap R t.algebra r)
        exact IsLocalization.Away.awayToAwayLeft_eq c.val b.val _ }
  have hφb : (q.imageTest t.algebra b).map ≫ ψb = φ := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro z
    change IsLocalization.Away.awayToAwayRight
      (S := Localization.Away b.val) (P := Localization.Away (b.val * c.val)) b.val c.val
      (algebraMap t.algebra (Localization.Away b.val) z) =
        algebraMap t.algebra (Localization.Away (b.val * c.val)) z
    exact IsLocalization.Away.awayToAwayRight_eq b.val c.val z
  have hφc : (q.imageTest t.algebra c).map ≫ ψc = φ := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro z
    change IsLocalization.Away.awayToAwayLeft
      (S := Localization.Away c.val) (P := Localization.Away (b.val * c.val)) c.val b.val
      (algebraMap t.algebra (Localization.Away c.val) z) =
        algebraMap t.algebra (Localization.Away (b.val * c.val)) z
    exact IsLocalization.Away.awayToAwayLeft_eq c.val b.val z
  have ha : IsUnit (algebraMap R B t.chart.val) := unit_map φ t.isUnit
  have hb : IsUnit (algebraMap R B (q.imageTest t.algebra b).chart.val) :=
    unit_map ψb (q.imageTest t.algebra b).isUnit
  have hc : IsUnit (algebraMap R B (q.imageTest t.algebra c).chart.val) :=
    unit_map ψc (q.imageTest t.algebra c).isUnit
  have hleft : SeriesPoint.map ψb.hom.toRingHom (q.localFamily y t b) =
      q.transportedValue y B (t.map ≫ φ) t.chart ha (q.imageTest t.algebra b).chart hb := by
    simpa only [localFamily, Category.assoc, hφb] using
      q.transportedValue_map y (t.map ≫ (q.imageTest t.algebra b).map) ψb t.chart
        (unit_map (q.imageTest t.algebra b).map t.isUnit) ha
        (q.imageTest t.algebra b).chart (q.imageTest t.algebra b).isUnit hb
  have hright : SeriesPoint.map ψc.hom.toRingHom (q.localFamily y t c) =
      q.transportedValue y B (t.map ≫ φ) t.chart ha (q.imageTest t.algebra c).chart hc := by
    simpa only [localFamily, Category.assoc, hφc] using
      q.transportedValue_map y (t.map ≫ (q.imageTest t.algebra c).map) ψc t.chart
        (unit_map (q.imageTest t.algebra c).map t.isUnit) ha
        (q.imageTest t.algebra c).chart (q.imageTest t.algebra c).isUnit hc
  exact hleft.trans ((q.transportedValue_independent y B (t.map ≫ φ) t.chart ha
    (q.imageTest t.algebra b).chart (q.imageTest t.algebra c).chart hb hc).trans hright.symm)

/-- Glue the actual matching tuples in each original chart. -/
def gluedValue {A : CommAlgCat.{v} R} (y : q.atlas.Point A) (t : X.ChartTest A) :
    X.ChartPoint t.algebra t.chart t.isUnit :=
  SeriesPoint.glueBasic (q.atlas.baseOpens t.algebra) (q.atlas.baseOpens_covers t.algebra)
    (q.localFamily y t) (q.localFamily_compatible y t)

/-- Each localization of the glued tuple is the prescribed transported tuple. -/
theorem gluedValue_local {A : CommAlgCat.{v} R} (y : q.atlas.Point A)
    (t : X.ChartTest A) (c : q.atlas.baseOpens t.algebra) :
    SeriesPoint.map (q.imageTest t.algebra c).map.hom.toRingHom (q.gluedValue y t) =
      q.localFamily y t c :=
  SeriesPoint.glueBasic_map (q.atlas.baseOpens t.algebra)
    (q.atlas.baseOpens_covers t.algebra) (q.localFamily y t) (q.localFamily_compatible y t) c

/-- The glued tuple recovers every finer-chart test, after any coefficient map. -/
theorem gluedValue_map {A C : CommAlgCat.{v} R} (y : q.atlas.Point A)
    (t : X.ChartTest A) (ψ : t.algebra ⟶ C)
    (ha : IsUnit (algebraMap R C t.chart.val)) (b : q.opens)
    (hb : IsUnit (algebraMap R C b.val)) :
    SeriesPoint.map ψ.hom.toRingHom (q.gluedValue y t) =
      q.transportedValue y C (t.map ≫ ψ) t.chart ha b hb := by
  let c : q.atlas.baseOpens t.algebra :=
    ⟨algebraMap R t.algebra b.val, ⟨b.val, b.property, rfl⟩⟩
  let w : q.atlas.ChartTest t.algebra := ⟨C, ψ, b, hb⟩
  let χ : (q.imageTest t.algebra c).algebra ⟶ C := q.atlas.testFactor w
  have htri : (q.imageTest t.algebra c).map ≫ χ = ψ :=
    q.atlas.localizationMap_testFactor w
  have hc : IsUnit (algebraMap R C (q.imageTest t.algebra c).chart.val) :=
    unit_map χ (q.imageTest t.algebra c).isUnit
  have hmap : SeriesPoint.map ψ.hom.toRingHom (q.gluedValue y t) =
      SeriesPoint.map χ.hom.toRingHom
        (SeriesPoint.map (q.imageTest t.algebra c).map.hom.toRingHom (q.gluedValue y t)) := by
    have h := (SeriesPoint.map_comp (q.imageTest t.algebra c).map.hom.toRingHom
      χ.hom.toRingHom (q.gluedValue y t)).symm
    change SeriesPoint.map ((q.imageTest t.algebra c).map ≫ χ).hom.toRingHom
      (q.gluedValue y t) = _ at h
    simpa only [htri] using h
  have hlocal := congrArg (SeriesPoint.map χ.hom.toRingHom) (q.gluedValue_local y t c)
  have hn : SeriesPoint.map χ.hom.toRingHom (q.localFamily y t c) =
      q.transportedValue y C (t.map ≫ ψ) t.chart ha (q.imageTest t.algebra c).chart hc := by
    simpa only [localFamily, Category.assoc, htri] using
      q.transportedValue_map y (t.map ≫ (q.imageTest t.algebra c).map) χ t.chart
        (unit_map (q.imageTest t.algebra c).map t.isUnit) ha
        (q.imageTest t.algebra c).chart (q.imageTest t.algebra c).isUnit hc
  exact hmap.trans (hlocal.trans (hn.trans
    (q.transportedValue_independent y C (t.map ≫ ψ) t.chart ha
      (q.imageTest t.algebra c).chart b hc hb)))

/-- Gluing in a fixed original chart commutes with every coefficient map. -/
theorem gluedValue_natural {A B C : CommAlgCat.{v} R} (y : q.atlas.Point A)
    (φ : A ⟶ B) (ψ : B ⟶ C) (a : X.opens)
    (ha : IsUnit (algebraMap R B a.val)) (ha' : IsUnit (algebraMap R C a.val)) :
    SeriesPoint.map ψ.hom.toRingHom (q.gluedValue y ⟨B, φ, a, ha⟩) =
      q.gluedValue y ⟨C, φ ≫ ψ, a, ha'⟩ := by
  apply SeriesPoint.ext_basic (q.atlas.baseOpens C) (q.atlas.baseOpens_covers C)
  intro c
  let w := q.imageTest C c
  have haC : IsUnit (algebraMap R w.algebra a.val) := unit_map w.map ha'
  have hl := q.gluedValue_map y ⟨B, φ, a, ha⟩ (ψ ≫ w.map) haC w.chart w.isUnit
  have hr : SeriesPoint.map w.map.hom.toRingHom (q.gluedValue y ⟨C, φ ≫ ψ, a, ha'⟩) =
      q.transportedValue y w.algebra (φ ≫ (ψ ≫ w.map)) a haC w.chart w.isUnit := by
    simpa only [Category.assoc] using
      q.gluedValue_map y ⟨C, φ ≫ ψ, a, ha'⟩ w.map haC w.chart w.isUnit
  exact ((SeriesPoint.map_comp ψ.hom.toRingHom w.map.hom.toRingHom
    (q.gluedValue y ⟨B, φ, a, ha⟩)).trans hl).trans hr.symm

/-- Glued tuples satisfy the actual original formal chart transitions. -/
theorem gluedValue_transition {A B : CommAlgCat.{v} R} (y : q.atlas.Point A)
    (φ : A ⟶ B) (a a' : X.opens)
    (ha : IsUnit (algebraMap R B a.val)) (ha' : IsUnit (algebraMap R B a'.val)) :
    X.transitionPoints B a a' ha ha' (q.gluedValue y ⟨B, φ, a, ha⟩) =
      q.gluedValue y ⟨B, φ, a', ha'⟩ := by
  apply SeriesPoint.ext_basic (q.atlas.baseOpens B) (q.atlas.baseOpens_covers B)
  intro c
  let w := q.imageTest B c
  have haC : IsUnit (algebraMap R w.algebra a.val) := unit_map w.map ha
  have haC' : IsUnit (algebraMap R w.algebra a'.val) := unit_map w.map ha'
  have hn := X.transitionPoints_natural w.map a a' ha ha' haC haC'
    (q.gluedValue y ⟨B, φ, a, ha⟩)
  simp only [pointMap_apply] at hn
  have hl := q.gluedValue_map y ⟨B, φ, a, ha⟩ w.map haC w.chart w.isUnit
  have hr := q.gluedValue_map y ⟨B, φ, a', ha'⟩ w.map haC' w.chart w.isUnit
  exact hn.trans ((congrArg (X.transitionPoints w.algebra a a' haC haC') hl).trans
    ((q.transportedValue_transition y w.algebra (φ ≫ w.map) a a' haC haC'
      w.chart w.isUnit).trans hr.symm))

/-- The constructed original-chart family has both required compatibilities. -/
theorem gluedValue_compatible {A : CommAlgCat.{v} R} (y : q.atlas.Point A) :
    X.Compatible (q.gluedValue y) := by
  constructor
  · intro B C φ ψ a hb hc
    exact (pointMap_apply (X.chart a) ψ hb hc _).trans
      (q.gluedValue_natural y φ ψ a hb hc)
  · intro B φ a b ha hb
    exact q.gluedValue_transition y φ a b ha hb

/-- Reconstruct a full original-atlas point by actual local coefficient gluing. -/
def fromPoints {A : CommAlgCat.{v} R} (y : q.atlas.Point A) : X.Point A :=
  ⟨q.gluedValue y, q.gluedValue_compatible y⟩

@[simp]
theorem fromPoints_apply {A : CommAlgCat.{v} R} (y : q.atlas.Point A)
    (t : X.ChartTest A) : (q.fromPoints y).val t = q.gluedValue y t := rfl

/-- Restriction followed by gluing recovers every original test component. -/
theorem gluedValue_onPoints {A : CommAlgCat.{v} R} (x : X.Point A)
    (t : X.ChartTest A) : q.gluedValue (q.onPoints A x) t = x.val t := by
  apply SeriesPoint.ext_basic (q.atlas.baseOpens t.algebra)
    (q.atlas.baseOpens_covers t.algebra)
  intro c
  let w := q.imageTest t.algebra c
  have ha : IsUnit (algebraMap R w.algebra t.chart.val) := unit_map w.map t.isUnit
  have hlocal := q.gluedValue_local (q.onPoints A x) t c
  have htransport : q.localFamily (q.onPoints A x) t c =
      x.val ⟨w.algebra, t.map ≫ w.map, t.chart, ha⟩ :=
    x.property.2 w.algebra (t.map ≫ w.map) (q.source w.chart) t.chart
      (q.source_unit w.algebra w.chart w.isUnit) ha
  have hmap : SeriesPoint.map w.map.hom.toRingHom (x.val t) =
      x.val ⟨w.algebra, t.map ≫ w.map, t.chart, ha⟩ :=
    (pointMap_apply (X.chart t.chart) w.map t.isUnit ha _).symm.trans
      (x.property.1 t.algebra w.algebra t.map w.map t.chart t.isUnit ha)
  exact hlocal.trans (htransport.trans hmap.symm)

/-- The constructed gluing is a left inverse to restriction of complete families. -/
@[simp]
theorem from_onPoints (A : CommAlgCat.{v} R) (x : X.Point A) :
    q.fromPoints (q.onPoints A x) = x := by
  apply Subtype.ext
  funext t
  exact q.gluedValue_onPoints x t

/-- The constructed gluing is a right inverse at every finer-chart test. -/
@[simp]
theorem on_fromPoints (A : CommAlgCat.{v} R) (y : q.atlas.Point A) :
    q.onPoints A (q.fromPoints y) = y := by
  apply Subtype.ext
  funext t
  change q.gluedValue y (q.restrictTest t) = y.val t
  have h := q.gluedValue_map y (q.restrictTest t) (𝟙 t.algebra)
    (q.source_unit t.algebra t.chart t.isUnit) t.chart t.isUnit
  change SeriesPoint.map (RingHom.id t.algebra) (q.gluedValue y (q.restrictTest t)) =
    q.transportedValue y t.algebra (t.map ≫ 𝟙 t.algebra) (q.source t.chart)
      (q.source_unit t.algebra t.chart t.isUnit) t.chart t.isUnit at h
  simp only [Category.comp_id] at h
  exact h.trans (X.transitionPoints_self t.algebra (q.source t.chart)
    (q.source_unit t.algebra t.chart t.isUnit) (y.val t))

/-- Actual varying-law atlas points are invariant under the constructed refinement. -/
def pointEquiv (A : CommAlgCat.{v} R) : X.Point A ≃ₗ[O] q.atlas.Point A :=
  { q.onPoints A with
    invFun := q.fromPoints
    left_inv := q.from_onPoints A
    right_inv := q.on_fromPoints A }

@[simp]
theorem pointEquiv_apply (A : CommAlgCat.{v} R) (x : X.Point A)
    (t : q.atlas.ChartTest A) :
    (q.pointEquiv A x).val t = x.val (q.restrictTest t) := rfl

@[simp]
theorem pointEquiv_symm_apply (A : CommAlgCat.{v} R) (y : q.atlas.Point A)
    (t : X.ChartTest A) :
    ((q.pointEquiv A).symm y).val t = q.gluedValue y t := rfl

/-- The point equivalence is natural in every coefficient algebra. -/
theorem pointEquiv_natural {A B : CommAlgCat.{v} R} (φ : A ⟶ B) (x : X.Point A) :
    q.atlas.mapPoints φ (q.pointEquiv A x) = q.pointEquiv B (X.mapPoints φ x) :=
  q.onPoints_natural φ x

/-- The constructed inverse gluing is natural in every coefficient algebra. -/
theorem fromPoints_natural {A B : CommAlgCat.{v} R} (φ : A ⟶ B) (y : q.atlas.Point A) :
    X.mapPoints φ (q.fromPoints y) = q.fromPoints (q.atlas.mapPoints φ y) := by
  apply (q.pointEquiv B).injective
  change q.onPoints B (X.mapPoints φ (q.fromPoints y)) =
    q.onPoints B (q.fromPoints (q.atlas.mapPoints φ y))
  rw [← q.onPoints_natural, q.on_fromPoints, q.on_fromPoints]

/-- The actual point functors of an atlas and its finer restriction are isomorphic. -/
def pointFunctorIso : X.pointFunctor ≅ q.atlas.pointFunctor :=
  NatIso.ofComponents (fun A => (q.pointEquiv A).toModuleIso) (by
    intro A B φ
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact q.pointEquiv_natural φ x)

/-- Refinement invariance also holds on actual algebras where pi is nilpotent. -/
def nilpPointFunctorIso (π : R) : X.nilpPointFunctor π ≅ q.atlas.nilpPointFunctor π :=
  Functor.isoWhiskerLeft (Nilp.forget R π) q.pointFunctorIso

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.CoverRefinement
