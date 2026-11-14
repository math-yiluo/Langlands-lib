import Langlands.Geometry.FormalGroup.AtlasRationalMorphism
import Langlands.Geometry.FormalGroup.AtlasOrderMorphism
import Langlands.Geometry.FormalGroup.OrderRationalMorphism

/-! # Rational formal atlas maps commuting with the full order -/

noncomputable section

universe u v w z

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable (F : Type z) [Field F] [Algebra O F]
variable {σ τ υ ω : Type} [Finite σ] [Finite τ] [Finite υ] [Finite ω]
variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ}
variable {Z : BasicAtlas O R υ} {W : BasicAtlas O R ω}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- Rational formal atlas maps satisfying every formal chart commutation equation. -/
def rationalHomSubmodule (E : OrderAction D X) (E' : OrderAction D Y)
    (h : X.opens = Y.opens) : Submodule F (BasicAtlas.RationalHom F X Y h) where
  carrier := {f | ∀ (A : CommAlgCat.{v} R) (b : Y.opens)
    (hb : IsUnit (algebraMap R A b.val)) (a : D),
    ModuleLaw.RationalHom.comp (BasicAtlas.RationalHom.onChart (X := X) (h := h) A b hb f)
      (ModuleLaw.RationalHom.ofHom
        (((E.chart (sourceChart h b)).map (coefficientLift (O := O) b.val A hb)).action a)) =
      ModuleLaw.RationalHom.comp
        (ModuleLaw.RationalHom.ofHom
          (((E'.chart b).map (coefficientLift (O := O) b.val A hb)).action a))
        (BasicAtlas.RationalHom.onChart (X := X) (h := h) A b hb f)}
  zero_mem' := by intro A b hb a; simp
  add_mem' := by
    intro f g hf hg A b hb a
    simp only [map_add, ModuleLaw.RationalHom.add_comp, ModuleLaw.RationalHom.comp_add,
      hf A b hb a, hg A b hb a]
  smul_mem' := by
    intro c f hf A b hb a
    simp only [map_smul, ModuleLaw.RationalHom.smul_comp, ModuleLaw.RationalHom.comp_smul,
      hf A b hb a]

/-- The full-order centralizer inside global rational formal atlas Hom. -/
def RationalHom (E : OrderAction D X) (E' : OrderAction D Y) (h : X.opens = Y.opens) :=
  ↥(rationalHomSubmodule F E E' h)

instance (E : OrderAction D X) (E' : OrderAction D Y) (h : X.opens = Y.opens) :
    AddCommGroup (RationalHom F E E' h) :=
  inferInstanceAs (AddCommGroup ↥(rationalHomSubmodule F E E' h))

instance (E : OrderAction D X) (E' : OrderAction D Y) (h : X.opens = Y.opens) :
    Module F (RationalHom F E E' h) :=
  inferInstanceAs (Module F ↥(rationalHomSubmodule F E E' h))

namespace RationalHom

variable {F}
variable {E : OrderAction D X} {E' : OrderAction D Y}
variable {E'' : OrderAction D Z} {E''' : OrderAction D W}
variable {h : X.opens = Y.opens} {k : Y.opens = Z.opens} {l : Z.opens = W.opens}

/-- Forget order commutation, retaining the actual global tensor map. -/
def toLinearMap : RationalHom F E E' h →ₗ[F] BasicAtlas.RationalHom F X Y h :=
  (rationalHomSubmodule F E E' h).subtype

theorem toLinearMap_injective : Function.Injective (toLinearMap (F := F) (E := E) (E' := E') (h := h)) :=
  Subtype.val_injective

@[ext]
theorem ext {f g : RationalHom F E E' h} (he : f.val = g.val) : f = g :=
  Subtype.ext he

/-- Evaluation is an actual order-equivariant rational coordinate map. -/
def onChart (f : RationalHom F E E' h) (A : CommAlgCat.{v} R) (b : Y.opens)
    (hb : IsUnit (algebraMap R A b.val)) :
    ModuleLaw.OrderAction.RationalHom F
      ((E.chart (sourceChart h b)).map (coefficientLift (O := O) b.val A hb))
      ((E'.chart b).map (coefficientLift (O := O) b.val A hb)) :=
  ⟨BasicAtlas.RationalHom.onChart (X := X) (h := h) A b hb f.val, f.property A b hb⟩

/-- The defining order-commutation equation on every test chart. -/
theorem commutes (f : RationalHom F E E' h) (A : CommAlgCat.{v} R) (b : Y.opens)
    (hb : IsUnit (algebraMap R A b.val)) (a : D) :
    ModuleLaw.RationalHom.comp (f.onChart A b hb).val
      (ModuleLaw.RationalHom.ofHom
        (((E.chart (sourceChart h b)).map (coefficientLift (O := O) b.val A hb)).action a)) =
      ModuleLaw.RationalHom.comp
        (ModuleLaw.RationalHom.ofHom
          (((E'.chart b).map (coefficientLift (O := O) b.val A hb)).action a))
        (f.onChart A b hb).val := f.property A b hb a

/-- Chart evaluation is F-linear inside the full-order coordinate centralizer. -/
def onChartLinear (A : CommAlgCat.{v} R) (b : Y.opens)
    (hb : IsUnit (algebraMap R A b.val)) :
    RationalHom F E E' h →ₗ[F] ModuleLaw.OrderAction.RationalHom F
      ((E.chart (sourceChart h b)).map (coefficientLift (O := O) b.val A hb))
      ((E'.chart b).map (coefficientLift (O := O) b.val A hb)) where
  toFun f := f.onChart A b hb
  map_add' f g := by
    apply ModuleLaw.OrderAction.RationalHom.ext
    exact (BasicAtlas.RationalHom.onChart (X := X) (h := h) A b hb).map_add f.val g.val
  map_smul' c f := by
    apply ModuleLaw.OrderAction.RationalHom.ext
    exact (BasicAtlas.RationalHom.onChart (X := X) (h := h) A b hb).map_smul c f.val

/-- Rationalize an actual integral full-order atlas homomorphism. -/
def ofHom (f : Hom E E' h) : RationalHom F E E' h :=
  ⟨BasicAtlas.RationalHom.ofHom f.val, by
    intro A b hb a
    change ModuleLaw.RationalHom.comp (ModuleLaw.RationalHom.ofHom (f.val.hom A b hb))
      (ModuleLaw.RationalHom.ofHom _) =
      ModuleLaw.RationalHom.comp (ModuleLaw.RationalHom.ofHom _)
        (ModuleLaw.RationalHom.ofHom (f.val.hom A b hb))
    rw [← ModuleLaw.RationalHom.ofHom_comp, f.commutes,
      ModuleLaw.RationalHom.ofHom_comp]⟩

/-- The rational formal identity commutes with every order element. -/
def id (E : OrderAction D X) : RationalHom F E E rfl :=
  ⟨BasicAtlas.RationalHom.id X, by
    intro A b hb a
    rw [BasicAtlas.RationalHom.onChart_id (F := F)]
    simp⟩

/-- Full-order composition is the inherited actual rational formal composition. -/
def comp (g : RationalHom F E' E'' k) (f : RationalHom F E E' h) :
    RationalHom F E E'' (h.trans k) :=
  ⟨BasicAtlas.RationalHom.comp g.val f.val, by
    intro A b hb a
    rw [BasicAtlas.RationalHom.onChart_comp (F := F)]
    exact ((g.onChart A b hb).comp (f.onChart A (sourceChart k b) hb)).commutes a⟩

@[simp]
theorem comp_val (g : RationalHom F E' E'' k) (f : RationalHom F E E' h) :
    (g.comp f).val = BasicAtlas.RationalHom.comp g.val f.val := rfl

@[simp]
theorem ofHom_val (f : Hom E E' h) :
    (ofHom (F := F) f).val = BasicAtlas.RationalHom.ofHom f.val := rfl

@[simp]
theorem id_val (E : OrderAction D X) :
    (id (F := F) E).val = BasicAtlas.RationalHom.id X := rfl

@[simp]
theorem comp_id (f : RationalHom F E E' h) : f.comp (id E) = f := by
  apply ext
  exact BasicAtlas.RationalHom.comp_id f.val

@[simp]
theorem id_comp (f : RationalHom F E E' h) : (id E').comp f = f := by
  apply ext
  exact BasicAtlas.RationalHom.id_comp f.val

theorem comp_assoc (q : RationalHom F E'' E''' l) (g : RationalHom F E' E'' k)
    (f : RationalHom F E E' h) : (q.comp g).comp f = q.comp (g.comp f) := by
  apply ext
  exact BasicAtlas.RationalHom.comp_assoc q.val g.val f.val

@[simp]
theorem comp_add (g : RationalHom F E' E'' k) (f₁ f₂ : RationalHom F E E' h) :
    g.comp (f₁ + f₂) = g.comp f₁ + g.comp f₂ := by
  apply ext
  exact BasicAtlas.RationalHom.comp_add g.val f₁.val f₂.val

@[simp]
theorem add_comp (g₁ g₂ : RationalHom F E' E'' k) (f : RationalHom F E E' h) :
    (g₁ + g₂).comp f = g₁.comp f + g₂.comp f := by
  apply ext
  exact BasicAtlas.RationalHom.add_comp g₁.val g₂.val f.val

@[simp]
theorem comp_smul (g : RationalHom F E' E'' k) (c : F) (f : RationalHom F E E' h) :
    g.comp (c • f) = c • g.comp f := by
  apply ext
  exact BasicAtlas.RationalHom.comp_smul g.val c f.val

@[simp]
theorem smul_comp (c : F) (g : RationalHom F E' E'' k) (f : RationalHom F E E' h) :
    (c • g).comp f = c • g.comp f := by
  apply ext
  exact BasicAtlas.RationalHom.smul_comp c g.val f.val

@[simp]
theorem comp_zero (g : RationalHom F E' E'' k) :
    g.comp (0 : RationalHom F E E' h) = 0 := by
  apply ext
  exact BasicAtlas.RationalHom.comp_zero g.val

@[simp]
theorem zero_comp (f : RationalHom F E E' h) :
    (0 : RationalHom F E' E'' k).comp f = 0 := by
  apply ext
  exact BasicAtlas.RationalHom.zero_comp f.val

/-- The full-order rational formal endomorphisms form a ring. -/
instance : Ring (RationalHom F E E rfl) where
  mul := comp
  one := id E
  mul_assoc := comp_assoc
  one_mul := id_comp
  mul_one := comp_id
  left_distrib := comp_add
  right_distrib := add_comp
  zero_mul := zero_comp
  mul_zero := comp_zero

/-- Composition of full-order rational maps is F-bilinear. -/
def compLinear : RationalHom F E' E'' k →ₗ[F]
    RationalHom F E E' h →ₗ[F] RationalHom F E E'' (h.trans k) where
  toFun g := {
    toFun := comp g
    map_add' := comp_add g
    map_smul' := comp_smul g }
  map_add' g₁ g₂ := by apply LinearMap.ext; intro f; exact add_comp g₁ g₂ f
  map_smul' c g := by apply LinearMap.ext; intro f; exact smul_comp c g f

@[simp]
theorem ofHom_id : ofHom (F := F) (Hom.id E) = id E := rfl

@[simp]
theorem ofHom_comp (g : Hom E' E'' k) (f : Hom E E' h) :
    ofHom (F := F) (g.comp f) = (ofHom g).comp (ofHom f) := by
  apply ext
  exact BasicAtlas.RationalHom.ofHom_comp g.val f.val

@[simp]
theorem onChart_id (E : OrderAction D X) (A : CommAlgCat.{v} R) (b : X.opens)
    (hb : IsUnit (algebraMap R A b.val)) :
    (id (F := F) E).onChart A b hb = ModuleLaw.OrderAction.RationalHom.id _ := by
  apply ModuleLaw.OrderAction.RationalHom.ext
  exact BasicAtlas.RationalHom.onChart_id (F := F) A b hb

@[simp]
theorem onChart_comp (g : RationalHom F E' E'' k) (f : RationalHom F E E' h)
    (A : CommAlgCat.{v} R) (b : Z.opens) (hb : IsUnit (algebraMap R A b.val)) :
    (g.comp f).onChart A b hb =
      (g.onChart A b hb).comp (f.onChart A (sourceChart k b) hb) := by
  apply ModuleLaw.OrderAction.RationalHom.ext
  exact BasicAtlas.RationalHom.onChart_comp g.val f.val A b hb

@[simp]
theorem onChart_ofHom (f : Hom E E' h) (A : CommAlgCat.{v} R) (b : Y.opens)
    (hb : IsUnit (algebraMap R A b.val)) :
    (ofHom (F := F) f).onChart A b hb =
      ModuleLaw.OrderAction.RationalHom.ofHom (f.onChart A b hb) := by
  apply ModuleLaw.OrderAction.RationalHom.ext
  exact BasicAtlas.RationalHom.onChart_ofHom A b hb f.val

end RationalHom

/-- Invertible rational atlas maps commuting with the full order. -/
structure QuasiIsogeny [IsDomain O] [IsFractionRing O F]
    (E : OrderAction D X) (E' : OrderAction D Y) (h : X.opens = Y.opens) where
  hom : RationalHom F E E' h
  inv : RationalHom F E' E h.symm
  inv_hom : inv.comp hom = RationalHom.id E
  hom_inv : hom.comp inv = RationalHom.id E'

namespace QuasiIsogeny

variable [IsDomain O] [IsFractionRing O F]
variable {F}
variable {E : OrderAction D X} {E' : OrderAction D Y} {E'' : OrderAction D Z}
variable {h : X.opens = Y.opens} {k : Y.opens = Z.opens}

/-- Forget the order while retaining both actual rational atlas maps. -/
def toAtlasQuasiIsogeny (f : QuasiIsogeny F E E' h) : BasicAtlas.QuasiIsogeny F X Y h where
  hom := f.hom.val
  inv := f.inv.val
  inv_hom := congrArg Subtype.val f.inv_hom
  hom_inv := congrArg Subtype.val f.hom_inv

/-- Invertible rational atlas maps need equivariance only on the forward map. -/
theorem inverse_commutes (f : BasicAtlas.QuasiIsogeny F X Y h)
    (hf : f.hom ∈ rationalHomSubmodule F E E' h) :
    f.inv ∈ rationalHomSubmodule F E' E h.symm := by
  intro A b hb a
  exact ModuleLaw.OrderAction.QuasiIsogeny.inverse_commutes
    (E := (E.chart b).map (coefficientLift (O := O) b.val A hb))
    (E' := (E'.chart (sourceChart h.symm b)).map (coefficientLift (O := O) b.val A hb))
    (f.onChart A (sourceChart h.symm b) hb) (hf A (sourceChart h.symm b) hb) a

/-- Upgrade a quasi-isogeny from full-order commutation of its forward map. -/
def ofAtlasQuasiIsogeny (f : BasicAtlas.QuasiIsogeny F X Y h)
    (hf : f.hom ∈ rationalHomSubmodule F E E' h) : QuasiIsogeny F E E' h where
  hom := ⟨f.hom, hf⟩
  inv := ⟨f.inv, inverse_commutes f hf⟩
  inv_hom := RationalHom.ext f.inv_hom
  hom_inv := RationalHom.ext f.hom_inv

@[simp]
theorem toAtlas_ofAtlasQuasiIsogeny (f : BasicAtlas.QuasiIsogeny F X Y h)
    (hf : f.hom ∈ rationalHomSubmodule F E E' h) :
    (ofAtlasQuasiIsogeny f hf).toAtlasQuasiIsogeny = f := by
  apply BasicAtlas.QuasiIsogeny.ext_hom
  rfl

/-- Identity order-equivariant quasi-isogeny. -/
def refl (E : OrderAction D X) : QuasiIsogeny F E E rfl where
  hom := RationalHom.id E
  inv := RationalHom.id E
  inv_hom := RationalHom.id_comp _
  hom_inv := RationalHom.id_comp _

/-- Reverse both maps. -/
def symm (f : QuasiIsogeny F E E' h) : QuasiIsogeny F E' E h.symm where
  hom := f.inv
  inv := f.hom
  inv_hom := f.hom_inv
  hom_inv := f.inv_hom

/-- Compose using actual full-order rational atlas maps. -/
def trans (f : QuasiIsogeny F E E' h) (g : QuasiIsogeny F E' E'' k) :
    QuasiIsogeny F E E'' (h.trans k) where
  hom := g.hom.comp f.hom
  inv := f.inv.comp g.inv
  inv_hom := by
    rw [RationalHom.comp_assoc, ← RationalHom.comp_assoc g.inv, g.inv_hom,
      RationalHom.id_comp, f.inv_hom]
  hom_inv := by
    rw [RationalHom.comp_assoc, ← RationalHom.comp_assoc f.hom, f.hom_inv,
      RationalHom.id_comp, g.hom_inv]

/-- Include every actual integral full-order atlas isomorphism. -/
def ofIso (f : Iso E E' h) : QuasiIsogeny F E E' h where
  hom := RationalHom.ofHom f.hom
  inv := RationalHom.ofHom f.inv
  inv_hom := by
    rw [← RationalHom.ofHom_comp, f.inv_hom, RationalHom.ofHom_id]
  hom_inv := by
    rw [← RationalHom.ofHom_comp, f.hom_inv, RationalHom.ofHom_id]

/-- The inverse is uniquely determined. -/
theorem inv_unique (f : QuasiIsogeny F E E' h) (g : RationalHom F E' E h.symm)
    (hg : g.comp f.hom = RationalHom.id E) : g = f.inv := by
  apply RationalHom.ext
  exact f.toAtlasQuasiIsogeny.inv_unique g.val (congrArg Subtype.val hg)

@[ext]
theorem ext_hom {f g : QuasiIsogeny F E E' h} (he : f.hom = g.hom) : f = g := by
  have hi : f.inv = g.inv := g.inv_unique f.inv (by rw [← he]; exact f.inv_hom)
  cases f
  cases g
  cases he
  cases hi
  rfl

/-- Chart evaluation retains both full-order rational maps and their inverse laws. -/
def onChart (f : QuasiIsogeny F E E' h) (A : CommAlgCat.{v} R) (b : Y.opens)
    (hb : IsUnit (algebraMap R A b.val)) :
    ModuleLaw.OrderAction.QuasiIsogeny F
      ((E.chart (sourceChart h b)).map (coefficientLift (O := O) b.val A hb))
      ((E'.chart b).map (coefficientLift (O := O) b.val A hb)) where
  hom := f.hom.onChart A b hb
  inv := f.inv.onChart A (sourceChart h b) hb
  inv_hom := by
    apply ModuleLaw.OrderAction.RationalHom.ext
    exact (f.toAtlasQuasiIsogeny.onChart A b hb).inv_hom
  hom_inv := by
    apply ModuleLaw.OrderAction.RationalHom.ext
    exact (f.toAtlasQuasiIsogeny.onChart A b hb).hom_inv

end QuasiIsogeny

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction
