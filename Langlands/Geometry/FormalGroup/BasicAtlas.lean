import Langlands.Geometry.FormalGroup.CoefficientCoherence
import Langlands.Geometry.FormalGroup.NilpotentAlgebras
import Mathlib.RingTheory.Localization.Away.Basic

/-! # Coordinate atlases on principal affine covers -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ : Type} [Finite σ]

attribute [local instance] coefficientAlgebra coefficientScalarTower

namespace BasicAtlas

/-- The unique coefficient extension from a principal open into a test algebra. -/
def coefficientLift (a : R) (A : CommAlgCat.{v} R)
    (ha : IsUnit (algebraMap R A a)) : Localization.Away a →ₐ[O] A :=
  IsLocalization.Away.liftAlgHom a (f := IsScalarTower.toAlgHom O R A) ha

@[simp]
theorem coefficientLift_algebraMap (a : R) (A : CommAlgCat.{v} R)
    (ha : IsUnit (algebraMap R A a)) (r : R) :
    coefficientLift (O := O) a A ha (algebraMap R (Localization.Away a) r) =
      algebraMap R A r := IsLocalization.Away.lift_eq a ha r

/-- Uniqueness of localization maps gives the actual coefficient triangle. -/
theorem coefficientLift_comp (a : R) {A B : CommAlgCat.{v} R} (φ : A ⟶ B)
    (ha : IsUnit (algebraMap R A a)) (hb : IsUnit (algebraMap R B a)) :
    (φ.hom.restrictScalars O).comp (coefficientLift (O := O) a A ha) = coefficientLift (O := O) a B hb := by
  apply AlgHom.ext
  have h : φ.hom.toRingHom.comp (coefficientLift (O := O) a A ha).toRingHom =
      (coefficientLift (O := O) a B hb).toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers a)
    ext r
    change φ.hom (coefficientLift (O := O) a A ha
      (algebraMap R (Localization.Away a) r)) =
        coefficientLift (O := O) a B hb (algebraMap R (Localization.Away a) r)
    rw [coefficientLift_algebraMap, coefficientLift_algebraMap, φ.hom.commutes]
  exact RingHom.congr_fun h

/-- The coefficient triangle identifies its two actual extended formal laws. -/
def coefficientTriangleIso {a : R} (M : ModuleLaw O (Localization.Away (a : R)) σ)
    {A B : CommAlgCat.{v} R} (φ : A ⟶ B)
    (ha : IsUnit (algebraMap R A a)) (hb : IsUnit (algebraMap R B a)) :
    Iso ((M.map (coefficientLift (O := O) a A ha)).map (φ.hom.restrictScalars O))
      (M.map (coefficientLift (O := O) a B hb)) :=
  Iso.ofIdenticalCoordinates
    (by
      change (M.groupLaw.addition.map (coefficientLift (O := O) a A ha).toRingHom).map
        φ.hom.toRingHom = M.groupLaw.addition.map (coefficientLift (O := O) a B hb).toRingHom
      rw [CoordinateMap.map_ringHom_comp]
      exact congrArg (fun f : Localization.Away a →ₐ[O] B => M.groupLaw.addition.map f.toRingHom)
        (coefficientLift_comp (O := O) a φ ha hb))
    (fun c => by
      change ((M.action c).toCoordinateMap.map (coefficientLift (O := O) a A ha).toRingHom).map
        φ.hom.toRingHom = (M.action c).toCoordinateMap.map
          (coefficientLift (O := O) a B hb).toRingHom
      rw [CoordinateMap.map_ringHom_comp]
      exact congrArg (fun f : Localization.Away a →ₐ[O] B => (M.action c).toCoordinateMap.map f.toRingHom)
        (coefficientLift_comp (O := O) a φ ha hb))

/-- The actual O-linear map on chart points induced by an R-algebra map. -/
def pointMap {a : R} (M : ModuleLaw O (Localization.Away (a : R)) σ)
    {A B : CommAlgCat.{v} R} (φ : A ⟶ B)
    (ha : IsUnit (algebraMap R A a)) (hb : IsUnit (algebraMap R B a)) :
    (M.map (coefficientLift (O := O) a A ha)).Point Empty →ₗ[O]
      (M.map (coefficientLift (O := O) a B hb)).Point Empty :=
  (coefficientTriangleIso M φ ha hb).hom.onPoints.comp
    ((M.map (coefficientLift (O := O) a A ha)).mapPoints (φ.hom.restrictScalars O))

@[simp]
theorem pointMap_apply {a : R} (M : ModuleLaw O (Localization.Away (a : R)) σ)
    {A B : CommAlgCat.{v} R} (φ : A ⟶ B)
    (ha : IsUnit (algebraMap R A a)) (hb : IsUnit (algebraMap R B a))
    (x : (M.map (coefficientLift (O := O) a A ha)).Point Empty) :
    pointMap M φ ha hb x = SeriesPoint.map φ.hom.toRingHom x := by
  change SeriesPoint.eval CoordinateMap.id (SeriesPoint.map φ.hom.toRingHom x) = _
  exact SeriesPoint.eval_id _

@[simp]
theorem pointMap_id {a : R} (M : ModuleLaw O (Localization.Away a) σ)
    (A : CommAlgCat.{v} R) (ha : IsUnit (algebraMap R A a))
    (x : (M.map (coefficientLift (O := O) a A ha)).Point Empty) :
    pointMap M (𝟙 A) ha ha x = x := by
  rw [pointMap_apply]
  exact SeriesPoint.map_id x

@[simp]
theorem pointMap_comp {a : R} (M : ModuleLaw O (Localization.Away a) σ)
    {A B C : CommAlgCat.{v} R} (φ : A ⟶ B) (ψ : B ⟶ C)
    (ha : IsUnit (algebraMap R A a)) (hb : IsUnit (algebraMap R B a))
    (hc : IsUnit (algebraMap R C a))
    (x : (M.map (coefficientLift (O := O) a A ha)).Point Empty) :
    pointMap M (φ ≫ ψ) ha hc x = pointMap M ψ hb hc (pointMap M φ ha hb x) := by
  rw [pointMap_apply, pointMap_apply, pointMap_apply]
  exact (SeriesPoint.map_comp φ.hom.toRingHom ψ.hom.toRingHom x).symm

/-- Unit conditions on principal opens persist under coefficient maps. -/
theorem unit_map {a : R} {A B : CommAlgCat.{v} R} (φ : A ⟶ B)
    (ha : IsUnit (algebraMap R A a)) : IsUnit (algebraMap R B a) := by
  have h := ha.map φ.hom.toRingHom
  change IsUnit (φ.hom (algebraMap R A a)) at h
  rwa [φ.hom.commutes] at h

end BasicAtlas

/-- Actual formal coordinate laws and natural transition isomorphisms on a
principal-open cover. The cover and its transition maps are part of the data. -/
structure BasicAtlas (O : Type u) [CommRing O] (R : Type v) [CommRing R]
    [Algebra O R] (σ : Type) [Finite σ] where
  opens : Set R
  covers : Ideal.span opens = ⊤
  chart : (a : opens) → ModuleLaw O (Localization.Away a.val) σ
  transition : ∀ (A : CommAlgCat.{v} R) (a b : opens)
    (ha : IsUnit (algebraMap R A a.val)) (hb : IsUnit (algebraMap R A b.val)),
    Iso ((chart a).map (BasicAtlas.coefficientLift (O := O) a.val A ha))
      ((chart b).map (BasicAtlas.coefficientLift (O := O) b.val A hb))
  transition_self : ∀ (A : CommAlgCat.{v} R) (a : opens)
    (ha : IsUnit (algebraMap R A a.val)),
    transition A a a ha ha = Iso.refl _
  transition_cocycle : ∀ (A : CommAlgCat.{v} R) (a b c : opens)
    (ha : IsUnit (algebraMap R A a.val)) (hb : IsUnit (algebraMap R A b.val))
    (hc : IsUnit (algebraMap R A c.val)),
    (transition A a b ha hb).trans (transition A b c hb hc) =
      transition A a c ha hc
  transition_natural : ∀ {A B : CommAlgCat.{v} R} (φ : A ⟶ B) (a b : opens)
    (ha : IsUnit (algebraMap R A a.val)) (hb : IsUnit (algebraMap R A b.val))
    (ha' : IsUnit (algebraMap R B a.val)) (hb' : IsUnit (algebraMap R B b.val)),
    ((transition A a b ha hb).hom.toHom.toCoordinateMap.map φ.hom.toRingHom) =
      (transition B a b ha' hb').hom.toHom.toCoordinateMap

namespace BasicAtlas

variable (X : BasicAtlas O R σ)

/-- The actual module of nilpotent points in one chart over a test algebra. -/
abbrev ChartPoint (A : CommAlgCat.{v} R) (a : X.opens)
    (ha : IsUnit (algebraMap R A a.val)) :=
  ((X.chart a).map (coefficientLift (O := O) a.val A ha)).Point Empty

instance chartPointAddCommGroup (A : CommAlgCat.{v} R) (a : X.opens)
    (ha : IsUnit (algebraMap R A a.val)) : AddCommGroup (X.ChartPoint A a ha) :=
  inferInstanceAs (AddCommGroup
    (((X.chart a).map (coefficientLift (O := O) a.val A ha)).Point Empty))

instance chartPointModule (A : CommAlgCat.{v} R) (a : X.opens)
    (ha : IsUnit (algebraMap R A a.val)) : Module O (X.ChartPoint A a ha) :=
  inferInstanceAs (Module O
    (((X.chart a).map (coefficientLift (O := O) a.val A ha)).Point Empty))

/-- Evaluation of a transition is an O-linear equivalence of nilpotent tuples. -/
def transitionPoints (A : CommAlgCat.{v} R) (a b : X.opens)
    (ha : IsUnit (algebraMap R A a.val)) (hb : IsUnit (algebraMap R A b.val)) :
    X.ChartPoint A a ha ≃ₗ[O] X.ChartPoint A b hb :=
  (X.transition A a b ha hb).onPoints

@[simp]
theorem transitionPoints_self (A : CommAlgCat.{v} R) (a : X.opens)
    (ha : IsUnit (algebraMap R A a.val)) (x : X.ChartPoint A a ha) :
    X.transitionPoints A a a ha ha x = x := by
  change (X.transition A a a ha ha).hom.onPoints x = x
  rw [X.transition_self]
  exact Hom.onPoints_id x

@[simp]
theorem transitionPoints_cocycle (A : CommAlgCat.{v} R) (a b c : X.opens)
    (ha : IsUnit (algebraMap R A a.val)) (hb : IsUnit (algebraMap R A b.val))
    (hc : IsUnit (algebraMap R A c.val)) (x : X.ChartPoint A a ha) :
    X.transitionPoints A b c hb hc (X.transitionPoints A a b ha hb x) =
      X.transitionPoints A a c ha hc x := by
  have h := congrArg (fun f => f.hom.onPoints x)
    (X.transition_cocycle A a b c ha hb hc)
  change (X.transition A b c hb hc).hom.onPoints
    ((X.transition A a b ha hb).hom.onPoints x) =
      (X.transition A a c ha hc).hom.onPoints x
  simpa only [Iso.trans, Hom.onPoints_comp] using h

/-- Formal coefficient naturality gives naturality on actual chart points. -/
theorem transitionPoints_natural {A B : CommAlgCat.{v} R} (φ : A ⟶ B)
    (a b : X.opens) (ha : IsUnit (algebraMap R A a.val))
    (hb : IsUnit (algebraMap R A b.val)) (ha' : IsUnit (algebraMap R B a.val))
    (hb' : IsUnit (algebraMap R B b.val)) (x : X.ChartPoint A a ha) :
    pointMap (X.chart b) φ hb hb' (X.transitionPoints A a b ha hb x) =
      X.transitionPoints B a b ha' hb' (pointMap (X.chart a) φ ha ha' x) := by
  simp only [pointMap_apply]
  change SeriesPoint A σ Empty at x
  change (SeriesPoint.eval _ x).map φ.hom.toRingHom = SeriesPoint.eval _ _
  rw [SeriesPoint.map_eval, X.transition_natural φ a b ha hb ha' hb']

/-- A test map into an algebra lying in a specified principal chart. -/
structure ChartTest (A : CommAlgCat.{v} R) where
  algebra : CommAlgCat.{v} R
  map : A ⟶ algebra
  chart : X.opens
  isUnit : IsUnit (algebraMap R algebra chart.val)

/-- A family assigns an actual nilpotent chart tuple after every test map. -/
abbrev Family (A : CommAlgCat.{v} R) :=
  (t : X.ChartTest A) → X.ChartPoint t.algebra t.chart t.isUnit

/-- Compatibility consists of coefficient naturality and formal chart changes. -/
def Compatible {A : CommAlgCat.{v} R} (x : X.Family A) : Prop :=
  (∀ (B C : CommAlgCat.{v} R) (φ : A ⟶ B) (ψ : B ⟶ C) (a : X.opens)
    (hb : IsUnit (algebraMap R B a.val)) (hc : IsUnit (algebraMap R C a.val)),
    pointMap (X.chart a) ψ hb hc (x ⟨B, φ, a, hb⟩) = x ⟨C, (φ ≫ ψ), a, hc⟩) ∧
  (∀ (B : CommAlgCat.{v} R) (φ : A ⟶ B) (a b : X.opens)
    (ha : IsUnit (algebraMap R B a.val)) (hb : IsUnit (algebraMap R B b.val)),
    X.transitionPoints B a b ha hb (x ⟨B, φ, a, ha⟩) = x ⟨B, φ, b, hb⟩)

/-- The simultaneous O-linear solution module of all compatibility equations. -/
def compatibleSubmodule (A : CommAlgCat.{v} R) : Submodule O (X.Family A) where
  carrier := X.Compatible
  zero_mem' := ⟨by intros; exact map_zero _, by intros; exact map_zero _⟩
  add_mem' := by
    intro x y hx hy
    constructor
    · intro B C φ ψ a hb hc
      change pointMap (X.chart a) ψ hb hc (x ⟨B, φ, a, hb⟩ + y ⟨B, φ, a, hb⟩) = _
      rw [map_add, hx.1 B C φ ψ a hb hc, hy.1 B C φ ψ a hb hc]
      rfl
    · intro B φ a b ha hb
      change X.transitionPoints B a b ha hb (x ⟨B, φ, a, ha⟩ + y ⟨B, φ, a, ha⟩) = _
      rw [map_add, hx.2 B φ a b ha hb, hy.2 B φ a b ha hb]
      rfl
  smul_mem' := by
    intro c x hx
    constructor
    · intro B C φ ψ a hb hc
      change pointMap (X.chart a) ψ hb hc (c • x ⟨B, φ, a, hb⟩) = _
      rw [map_smul, hx.1 B C φ ψ a hb hc]
      rfl
    · intro B φ a b ha hb
      change X.transitionPoints B a b ha hb (c • x ⟨B, φ, a, ha⟩) = _
      rw [map_smul, hx.2 B φ a b ha hb]
      rfl

/-- Glued points are compatible families of actual nilpotent coordinate tuples. -/
abbrev Point (A : CommAlgCat.{v} R) := X.compatibleSubmodule A

/-- Evaluation in a specified test chart is an actual O-linear map. -/
def evaluation (A : CommAlgCat.{v} R) (t : X.ChartTest A) :
    X.Point A →ₗ[O] X.ChartPoint t.algebra t.chart t.isUnit where
  toFun x := x.val t
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Coefficient extension of glued points by precomposing their test maps. -/
def mapPoints {A B : CommAlgCat.{v} R} (φ : A ⟶ B) :
    X.Point A →ₗ[O] X.Point B where
  toFun x := ⟨fun t => x.val ⟨t.algebra, φ ≫ t.map, t.chart, t.isUnit⟩,
    ⟨by
      intro C D ψ χ a hc hd
      exact (x.property.1 C D (φ ≫ ψ) χ a hc hd).trans
        (congrArg (β := X.ChartPoint D a hd) (fun f : A ⟶ D => (x.val ⟨D, f, a, hd⟩ : X.ChartPoint D a hd)) (Category.assoc φ ψ χ)),
    by
      intro C ψ a b ha hb
      exact x.property.2 C (φ ≫ ψ) a b ha hb⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem mapPoints_id (A : CommAlgCat.{v} R) (x : X.Point A) :
    X.mapPoints (𝟙 A) x = x := by
  apply Subtype.ext
  funext t
  change x.val ⟨t.algebra, 𝟙 A ≫ t.map, t.chart, t.isUnit⟩ = x.val t
  exact congrArg (β := X.ChartPoint t.algebra t.chart t.isUnit) (fun f : A ⟶ t.algebra =>
      (x.val ⟨t.algebra, f, t.chart, t.isUnit⟩ : X.ChartPoint t.algebra t.chart t.isUnit))
    (Category.id_comp t.map)

@[simp]
theorem mapPoints_comp {A B C : CommAlgCat.{v} R} (φ : A ⟶ B) (ψ : B ⟶ C)
    (x : X.Point A) :
    X.mapPoints (φ ≫ ψ) x = X.mapPoints ψ (X.mapPoints φ x) := by
  apply Subtype.ext
  funext t
  change x.val ⟨t.algebra, (φ ≫ ψ) ≫ t.map, t.chart, t.isUnit⟩ =
    x.val ⟨t.algebra, φ ≫ (ψ ≫ t.map), t.chart, t.isUnit⟩
  exact congrArg (β := X.ChartPoint t.algebra t.chart t.isUnit) (fun f : A ⟶ t.algebra =>
      (x.val ⟨t.algebra, f, t.chart, t.isUnit⟩ : X.ChartPoint t.algebra t.chart t.isUnit))
    (Category.assoc φ ψ t.map)

/-- The module-valued functor constructed from the actual atlas equations. -/
def pointFunctor : CommAlgCat.{v} R ⥤ ModuleCat.{v + 1} O where
  obj A := ModuleCat.of O (X.Point A)
  map φ := ModuleCat.ofHom (X.mapPoints φ)
  map_id A := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact X.mapPoints_id A x
  map_comp φ ψ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact X.mapPoints_comp φ ψ x

/-- The constructed functor restricted to the actual nilpotent-algebra category. -/
def nilpPointFunctor (π : R) : Nilp.{v, v} R π ⥤ ModuleCat.{v + 1} O :=
  Nilp.forget R π ⋙ X.pointFunctor

/-- A tuple in a chart which contains A extends to a compatible atlas family. -/
def ofChart {A : CommAlgCat.{v} R} (a : X.opens)
    (ha : IsUnit (algebraMap R A a.val)) : X.ChartPoint A a ha →ₗ[O] X.Point A where
  toFun x := ⟨fun t => X.transitionPoints t.algebra a t.chart (unit_map t.map ha) t.isUnit
    (pointMap (X.chart a) t.map ha (unit_map t.map ha) x),
    ⟨by
      intro B C φ ψ b hb hc
      rw [X.transitionPoints_natural ψ a b (unit_map φ ha) hb
        (unit_map (φ ≫ ψ) ha) hc]
      rw [← pointMap_comp],
    by
      intro B φ b c hb hc
      exact X.transitionPoints_cocycle B a b c (unit_map φ ha) hb hc _⟩⟩
  map_add' x y := by
    apply Subtype.ext
    funext t
    change X.transitionPoints _ _ _ _ _ (pointMap _ _ _ _ (x + y)) = _
    rw [map_add, map_add]
    rfl
  map_smul' c x := by
    apply Subtype.ext
    funext t
    change X.transitionPoints _ _ _ _ _ (pointMap _ _ _ _ (c • x)) = _
    rw [map_smul, map_smul]
    rfl

/-- Glued points recover the actual chart tuples whenever that chart contains A. -/
def chartEquiv {A : CommAlgCat.{v} R} (a : X.opens)
    (ha : IsUnit (algebraMap R A a.val)) : X.Point A ≃ₗ[O] X.ChartPoint A a ha where
  toFun x := x.val ⟨A, 𝟙 A, a, ha⟩
  invFun := X.ofChart a ha
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv x := by
    apply Subtype.ext
    funext t
    change X.transitionPoints t.algebra a t.chart (unit_map t.map ha) t.isUnit
      (pointMap (X.chart a) t.map ha (unit_map t.map ha)
        (x.val ⟨A, 𝟙 A, a, ha⟩)) = x.val t
    have hn := x.property.1 A t.algebra (𝟙 A) t.map a ha (unit_map t.map ha)
    rw [Category.id_comp] at hn
    rw [hn]
    exact x.property.2 t.algebra t.map a t.chart (unit_map t.map ha) t.isUnit
  right_inv x := by
    change X.transitionPoints A a a (unit_map (𝟙 A) ha) ha
      (pointMap (X.chart a) (𝟙 A) ha (unit_map (𝟙 A) ha) x) = x
    rw [pointMap_id, X.transitionPoints_self]

end BasicAtlas

end Langlands.FormalGroup.ModuleLaw
