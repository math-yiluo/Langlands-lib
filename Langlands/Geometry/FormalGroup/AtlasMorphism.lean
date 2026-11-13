import Langlands.Geometry.FormalGroup.BasicAtlas

/-! # Formal morphisms between atlases on the same principal cover -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ τ υ ω : Type} [Finite σ] [Finite τ] [Finite υ] [Finite ω]

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- Identify chart indices using equality of their principal-open covers. -/
abbrev sourceChart {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ}
    (h : X.opens = Y.opens) (b : Y.opens) : X.opens :=
  ⟨b.val, h.symm ▸ b.property⟩

/-- Actual formal O-linear chart maps, natural in coefficients and commuting
with the formal transitions, for two atlases on the same principal cover. -/
structure Hom (X : BasicAtlas O R σ) (Y : BasicAtlas O R τ)
    (h : X.opens = Y.opens) where
  hom : ∀ (A : CommAlgCat.{v} R) (b : Y.opens)
    (hb : IsUnit (algebraMap R A b.val)),
    ModuleLaw.Hom
      ((X.chart (sourceChart h b)).map (coefficientLift (O := O) b.val A hb))
      ((Y.chart b).map (coefficientLift (O := O) b.val A hb))
  natural : ∀ {A B : CommAlgCat.{v} R} (φ : A ⟶ B) (b : Y.opens)
    (ha : IsUnit (algebraMap R A b.val)) (hb : IsUnit (algebraMap R B b.val)),
    ((hom A b ha).toHom.toCoordinateMap.map φ.hom.toRingHom) =
      (hom B b hb).toHom.toCoordinateMap
  transition : ∀ (A : CommAlgCat.{v} R) (b c : Y.opens)
    (hb : IsUnit (algebraMap R A b.val)) (hc : IsUnit (algebraMap R A c.val)),
    (Y.transition A b c hb hc).hom.comp (hom A b hb) =
      (hom A c hc).comp
        (X.transition A (sourceChart h b) (sourceChart h c) hb hc).hom

namespace Hom

variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ}
variable {Z : BasicAtlas O R υ} {W : BasicAtlas O R ω}
variable {h : X.opens = Y.opens} {k : Y.opens = Z.opens} {l : Z.opens = W.opens}

/-- Equality of formal atlas maps is detected on the actual chart maps. -/
@[ext]
theorem ext {f g : Hom X Y h} (he : ∀ A b hb, f.hom A b hb = g.hom A b hb) :
    f = g := by
  cases f with
  | mk f fn ft =>
    cases g with
    | mk g gn gt =>
      have hh : f = g := funext (fun A => funext (fun b => funext (he A b)))
      cases hh
      rfl

/-- Formal coefficient naturality implies naturality on chart tuples. -/
theorem onChart_natural (f : Hom X Y h) {A B : CommAlgCat.{v} R} (φ : A ⟶ B)
    (b : Y.opens) (ha : IsUnit (algebraMap R A b.val))
    (hb : IsUnit (algebraMap R B b.val))
    (x : X.ChartPoint A (sourceChart h b) ha) :
    pointMap (Y.chart b) φ ha hb ((f.hom A b ha).onPoints x) =
      (f.hom B b hb).onPoints (pointMap (X.chart (sourceChart h b)) φ ha hb x) := by
  simp only [pointMap_apply]
  change SeriesPoint A σ Empty at x
  change (SeriesPoint.eval _ x).map φ.hom.toRingHom = SeriesPoint.eval _ _
  rw [SeriesPoint.map_eval, f.natural φ b ha hb]

/-- The transition square also commutes on actual nilpotent chart tuples. -/
theorem onChart_transition (f : Hom X Y h) (A : CommAlgCat.{v} R) (b c : Y.opens)
    (hb : IsUnit (algebraMap R A b.val)) (hc : IsUnit (algebraMap R A c.val))
    (x : X.ChartPoint A (sourceChart h b) hb) :
    Y.transitionPoints A b c hb hc ((f.hom A b hb).onPoints x) =
      (f.hom A c hc).onPoints
        (X.transitionPoints A (sourceChart h b) (sourceChart h c) hb hc x) := by
  have he := congrArg (fun g => g.onPoints x) (f.transition A b c hb hc)
  change (Y.transition A b c hb hc).hom.onPoints ((f.hom A b hb).onPoints x) =
    (f.hom A c hc).onPoints
      ((X.transition A (sourceChart h b) (sourceChart h c) hb hc).hom.onPoints x)
  simpa only [ModuleLaw.Hom.onPoints_comp] using he

/-- Apply the actual formal maps to every component of a compatible family. -/
def onPoints (f : Hom X Y h) (A : CommAlgCat.{v} R) :
    X.Point A →ₗ[O] Y.Point A where
  toFun x := ⟨fun t => (f.hom t.algebra t.chart t.isUnit).onPoints
    (x.val ⟨t.algebra, t.map, sourceChart h t.chart, t.isUnit⟩),
    ⟨by
      intro B C φ ψ b hb hc
      rw [f.onChart_natural ψ b hb hc, x.property.1 B C φ ψ (sourceChart h b) hb hc],
    by
      intro B φ b c hb hc
      rw [f.onChart_transition B b c hb hc,
        x.property.2 B φ (sourceChart h b) (sourceChart h c) hb hc]⟩⟩
  map_add' x y := by
    apply Subtype.ext
    funext t
    exact (f.hom t.algebra t.chart t.isUnit).onPoints.map_add _ _
  map_smul' a x := by
    apply Subtype.ext
    funext t
    exact (f.hom t.algebra t.chart t.isUnit).onPoints.map_smul a _

@[simp]
theorem onPoints_apply (f : Hom X Y h) (A : CommAlgCat.{v} R)
    (x : X.Point A) (t : Y.ChartTest A) :
    (f.onPoints A x).val t = (f.hom t.algebra t.chart t.isUnit).onPoints
      (x.val ⟨t.algebra, t.map, sourceChart h t.chart, t.isUnit⟩) := rfl

/-- The induced maps on compatible families commute with coefficient extension. -/
theorem onPoints_natural (f : Hom X Y h) {A B : CommAlgCat.{v} R} (φ : A ⟶ B)
    (x : X.Point A) :
    Y.mapPoints φ (f.onPoints A x) = f.onPoints B (X.mapPoints φ x) := by
  apply Subtype.ext
  funext t
  rfl

/-- A constructed natural transformation between the module-valued point functors. -/
def pointNatTrans (f : Hom X Y h) : X.pointFunctor ⟶ Y.pointFunctor where
  app A := ModuleCat.ofHom (f.onPoints A)
  naturality A B φ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (f.onPoints_natural φ x).symm

/-- Identity formal map in every chart. -/
def id (X : BasicAtlas O R σ) : Hom X X rfl where
  hom A b hb := ModuleLaw.Hom.id _
  natural φ b ha hb := CoordinateMap.map_id _
  transition A b c hb hc := by simp

/-- Compose the actual formal maps, with the right map applied first. -/
def comp (g : Hom Y Z k) (f : Hom X Y h) : Hom X Z (h.trans k) where
  hom A c hc := (g.hom A c hc).comp (f.hom A (sourceChart k c) hc)
  natural φ c ha hb := by
    change
      ((g.hom _ c ha).toHom.toCoordinateMap.comp
        (f.hom _ (sourceChart k c) ha).toHom.toCoordinateMap).map φ.hom.toRingHom = _
    rw [CoordinateMap.map_comp, g.natural φ c ha hb,
      f.natural φ (sourceChart k c) ha hb]
    rfl
  transition A b c hb hc := by
    rw [← ModuleLaw.Hom.comp_assoc, g.transition A b c hb hc,
      ModuleLaw.Hom.comp_assoc, f.transition A (sourceChart k b) (sourceChart k c) hb hc,
      ← ModuleLaw.Hom.comp_assoc]

@[simp]
theorem onPoints_id (X : BasicAtlas O R σ) (A : CommAlgCat.{v} R) (x : X.Point A) :
    (id X).onPoints A x = x := by
  apply Subtype.ext
  funext t
  exact ModuleLaw.Hom.onPoints_id _

@[simp]
theorem onPoints_comp (g : Hom Y Z k) (f : Hom X Y h) (A : CommAlgCat.{v} R)
    (x : X.Point A) :
    (g.comp f).onPoints A x = g.onPoints A (f.onPoints A x) := by
  apply Subtype.ext
  funext t
  exact ModuleLaw.Hom.onPoints_comp _ _ _

@[simp]
theorem comp_id (f : Hom X Y h) : f.comp (id X) = f := by
  apply ext
  intro A b hb
  exact ModuleLaw.Hom.comp_id _

@[simp]
theorem id_comp (f : Hom X Y h) : (id Y).comp f = f := by
  apply ext
  intro A b hb
  exact ModuleLaw.Hom.id_comp _

theorem comp_assoc (q : Hom Z W l) (g : Hom Y Z k) (f : Hom X Y h) :
    (q.comp g).comp f = q.comp (g.comp f) := by
  apply ext
  intro A b hb
  exact ModuleLaw.Hom.comp_assoc _ _ _

end Hom

end Langlands.FormalGroup.ModuleLaw.BasicAtlas
