import Langlands.Geometry.FormalGroup.AtlasOrderAction
import Mathlib.CategoryTheory.Whiskering

/-! # Order-linear formal maps between coordinate atlases -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {σ τ υ ω : Type} [Finite σ] [Finite τ] [Finite υ] [Finite ω]
variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ}
variable {Z : BasicAtlas O R υ} {W : BasicAtlas O R ω}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- Actual same-cover atlas maps commuting with every formal order action. -/
def Hom (E : OrderAction D X) (E' : OrderAction D Y) (h : X.opens = Y.opens) :=
  {f : BasicAtlas.Hom X Y h // ∀ (A : CommAlgCat.{v} R) (b : Y.opens)
    (hb : IsUnit (algebraMap R A b.val)) (a : D),
    (f.hom A b hb).comp
      (((E.chart (sourceChart h b)).map (coefficientLift (O := O) b.val A hb)).action a) =
      (((E'.chart b).map (coefficientLift (O := O) b.val A hb)).action a).comp
        (f.hom A b hb)}

namespace Hom

variable {E : OrderAction D X} {E' : OrderAction D Y}
variable {E'' : OrderAction D Z} {E''' : OrderAction D W}
variable {h : X.opens = Y.opens} {k : Y.opens = Z.opens} {l : Z.opens = W.opens}

/-- The defining commutation is an equality of actual formal maps. -/
theorem commutes (f : Hom E E' h) (A : CommAlgCat.{v} R) (b : Y.opens)
    (hb : IsUnit (algebraMap R A b.val)) (a : D) :
    (f.val.hom A b hb).comp
      (((E.chart (sourceChart h b)).map (coefficientLift (O := O) b.val A hb)).action a) =
      (((E'.chart b).map (coefficientLift (O := O) b.val A hb)).action a).comp
        (f.val.hom A b hb) := f.property A b hb a

/-- Each chart map is an order-linear formal homomorphism. -/
def onChart (f : Hom E E' h) (A : CommAlgCat.{v} R) (b : Y.opens)
    (hb : IsUnit (algebraMap R A b.val)) :
    ModuleLaw.OrderAction.Hom
      ((E.chart (sourceChart h b)).map (coefficientLift (O := O) b.val A hb))
      ((E'.chart b).map (coefficientLift (O := O) b.val A hb)) :=
  ⟨f.val.hom A b hb, f.commutes A b hb⟩

/-- Evaluate the formal chart maps on compatible families, retaining D-linearity. -/
def onPoints (f : Hom E E' h) (A : CommAlgCat.{v} R) :
    E.Point A →ₗ[D] E'.Point A where
  toFun := f.val.onPoints A
  map_add' := (f.val.onPoints A).map_add
  map_smul' a x := by
    apply Subtype.ext
    funext t
    exact (f.onChart t.algebra t.chart t.isUnit).onPoints.map_smul a
      (x.val ⟨t.algebra, t.map, sourceChart h t.chart, t.isUnit⟩)

@[simp]
theorem onPoints_apply (f : Hom E E' h) (A : CommAlgCat.{v} R)
    (x : E.Point A) (t : Y.ChartTest A) :
    (f.onPoints A x).val t =
      (f.onChart t.algebra t.chart t.isUnit).onPoints
        (x.val ⟨t.algebra, t.map, sourceChart h t.chart, t.isUnit⟩) := rfl

/-- Chart evaluation of a family map is evaluation of the actual chart map. -/
theorem chartEquiv_onPoints (f : Hom E E' h) (A : CommAlgCat.{v} R) (b : Y.opens)
    (hb : IsUnit (algebraMap R A b.val)) (x : E.Point A) :
    E'.chartEquiv b hb (f.onPoints A x) =
      (f.onChart A b hb).onPoints (E.chartEquiv (sourceChart h b) hb x) := rfl

/-- The D-linear family maps are natural in the coefficient algebra. -/
theorem onPoints_natural (f : Hom E E' h) {A B : CommAlgCat.{v} R} (φ : A ⟶ B)
    (x : E.Point A) :
    E'.mapPoints φ (f.onPoints A x) = f.onPoints B (E.mapPoints φ x) :=
  f.val.onPoints_natural φ x

/-- Natural transformation of the actual order-module point functors. -/
def pointNatTrans (f : Hom E E' h) : E.pointFunctor ⟶ E'.pointFunctor where
  app A := ModuleCat.ofHom (f.onPoints A)
  naturality A B φ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (f.onPoints_natural φ x).symm

/-- Restrict the constructed natural transformation to Nilp. -/
def nilpPointNatTrans (f : Hom E E' h) (π : R) :
    E.nilpPointFunctor π ⟶ E'.nilpPointFunctor π :=
  Functor.whiskerLeft (Nilp.forget R π) f.pointNatTrans

/-- The identity formal atlas map commutes with the full order. -/
def id (E : OrderAction D X) : Hom E E rfl :=
  ⟨BasicAtlas.Hom.id X, by intro A b hb a; simp [BasicAtlas.Hom.id]⟩

/-- Composition uses the composition of the actual same-cover formal maps. -/
def comp (g : Hom E' E'' k) (f : Hom E E' h) : Hom E E'' (h.trans k) :=
  ⟨g.val.comp f.val, by
    intro A c hc a
    change ((g.val.hom A c hc).comp (f.val.hom A (sourceChart k c) hc)).comp
      (((E.chart (sourceChart h (sourceChart k c))).map
        (coefficientLift (O := O) c.val A hc)).action a) =
      (((E''.chart c).map (coefficientLift (O := O) c.val A hc)).action a).comp
        ((g.val.hom A c hc).comp (f.val.hom A (sourceChart k c) hc))
    rw [ModuleLaw.Hom.comp_assoc, f.commutes,
      ← ModuleLaw.Hom.comp_assoc, g.commutes, ModuleLaw.Hom.comp_assoc]⟩

@[simp]
theorem onPoints_id (E : OrderAction D X) (A : CommAlgCat.{v} R) (x : E.Point A) :
    (id E).onPoints A x = x :=
  BasicAtlas.Hom.onPoints_id X A x

@[simp]
theorem onPoints_comp (g : Hom E' E'' k) (f : Hom E E' h) (A : CommAlgCat.{v} R)
    (x : E.Point A) :
    (g.comp f).onPoints A x = g.onPoints A (f.onPoints A x) :=
  BasicAtlas.Hom.onPoints_comp g.val f.val A x

@[simp]
theorem comp_id (f : Hom E E' h) : f.comp (id E) = f := by
  apply Subtype.ext
  exact BasicAtlas.Hom.comp_id f.val

@[simp]
theorem id_comp (f : Hom E E' h) : (id E').comp f = f := by
  apply Subtype.ext
  exact BasicAtlas.Hom.id_comp f.val

theorem comp_assoc (q : Hom E'' E''' l) (g : Hom E' E'' k) (f : Hom E E' h) :
    (q.comp g).comp f = q.comp (g.comp f) := by
  apply Subtype.ext
  exact BasicAtlas.Hom.comp_assoc q.val g.val f.val

end Hom

/-- Isomorphisms are two actual order-linear atlas maps with formal inverse laws. -/
structure Iso (E : OrderAction D X) (E' : OrderAction D Y) (h : X.opens = Y.opens) where
  hom : Hom E E' h
  inv : Hom E' E h.symm
  inv_hom : inv.comp hom = Hom.id E
  hom_inv : hom.comp inv = Hom.id E'

namespace Iso

variable {E : OrderAction D X} {E' : OrderAction D Y} {E'' : OrderAction D Z}
variable {h : X.opens = Y.opens} {k : Y.opens = Z.opens}

/-- The formal inverse equations induce a D-linear equivalence of actual families. -/
def onPoints (f : Iso E E' h) (A : CommAlgCat.{v} R) :
    E.Point A ≃ₗ[D] E'.Point A where
  toFun := f.hom.onPoints A
  invFun := f.inv.onPoints A
  map_add' := (f.hom.onPoints A).map_add
  map_smul' := (f.hom.onPoints A).map_smul
  left_inv x := by rw [← Hom.onPoints_comp, f.inv_hom, Hom.onPoints_id]
  right_inv x := by rw [← Hom.onPoints_comp, f.hom_inv, Hom.onPoints_id]

/-- An actual atlas isomorphism gives a natural isomorphism of D-module functors. -/
def pointNatIso (f : Iso E E' h) : E.pointFunctor ≅ E'.pointFunctor :=
  NatIso.ofComponents (fun A => (f.onPoints A).toModuleIso) (by
    intro A B φ
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (f.hom.onPoints_natural φ x).symm)

/-- The same constructed natural isomorphism over Nilp. -/
def nilpPointNatIso (f : Iso E E' h) (π : R) :
    E.nilpPointFunctor π ≅ E'.nilpPointFunctor π :=
  Functor.isoWhiskerLeft (Nilp.forget R π) f.pointNatIso

/-- Identity atlas isomorphism. -/
def refl (E : OrderAction D X) : Iso E E rfl where
  hom := Hom.id E
  inv := Hom.id E
  inv_hom := Hom.comp_id _
  hom_inv := Hom.comp_id _

/-- Reverse both actual formal maps. -/
def symm (f : Iso E E' h) : Iso E' E h.symm where
  hom := f.inv
  inv := f.hom
  inv_hom := f.hom_inv
  hom_inv := f.inv_hom

/-- Compose actual atlas isomorphisms. -/
def trans (f : Iso E E' h) (g : Iso E' E'' k) : Iso E E'' (h.trans k) where
  hom := g.hom.comp f.hom
  inv := f.inv.comp g.inv
  inv_hom := by
    rw [Hom.comp_assoc, ← Hom.comp_assoc g.inv, g.inv_hom, Hom.id_comp, f.inv_hom]
  hom_inv := by
    rw [Hom.comp_assoc, ← Hom.comp_assoc f.hom, f.hom_inv, Hom.id_comp, g.hom_inv]

end Iso

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction
