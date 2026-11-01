import Langlands.Geometry.EtaleCohomologyAction

/-! # Group-labelled morphisms of small-etale objects -/

noncomputable section

universe u w

namespace Langlands.Geometry.EtaleTransport

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open EtaleCohomologyAction

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {Y : Scheme.{u}} {G : Type w} [Group G]
variable (ρ : G →* (Aut Y)ᵐᵒᵖ)

/-- Small-etale objects, with a category of group-labelled scheme maps. -/
structure Object (ρ : G →* (Aut Y)ᵐᵒᵖ) where
  etale : Y.Etale

namespace Object

variable {ρ}

/-- A semilinear scheme map together with its specified group label. -/
structure Hom (U V : Object ρ) where
  label : G
  left : U.etale.left ⟶ V.etale.left
  w : left ≫ V.etale.hom = U.etale.hom ≫ (aut ρ label).hom

@[ext]
theorem Hom.ext {U V : Object ρ} {f g : Hom U V}
    (hl : f.label = g.label) (hm : f.left = g.left) : f = g := by
  cases f
  cases g
  cases hl
  cases hm
  rfl

/-- The identity-labelled identity scheme map. -/
def Hom.id (U : Object ρ) : Hom U U where
  label := 1
  left := 𝟙 _
  w := by rw [aut_one]; simp

/-- Compose scheme maps and multiply labels in their order of composition. -/
def Hom.comp {U V W : Object ρ} (f : Hom U V) (g : Hom V W) : Hom U W where
  label := f.label * g.label
  left := f.left ≫ g.left
  w := by
    rw [Category.assoc, g.w, ← Category.assoc, f.w, Category.assoc, aut_mul]
    rfl

instance : Category (Object ρ) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp _f := Hom.ext (one_mul _) (Category.id_comp _)
  comp_id _f := Hom.ext (mul_one _) (Category.comp_id _)
  assoc _f _g _h := Hom.ext (mul_assoc _ _ _) (Category.assoc _ _ _)

@[simp] theorem id_label (U : Object ρ) : (𝟙 U : U ⟶ U).label = 1 := rfl
@[simp] theorem id_left (U : Object ρ) : (𝟙 U : U ⟶ U).left = 𝟙 U.etale.left := rfl
@[simp] theorem comp_label {U V W : Object ρ} (f : U ⟶ V) (g : V ⟶ W) :
    (f ≫ g).label = f.label * g.label := rfl
@[simp] theorem comp_left {U V W : Object ρ} (f : U ⟶ V) (g : V ⟶ W) :
    (f ≫ g).left = f.left ≫ g.left := rfl

end Object

/-- Ordinary small-etale maps are precisely the maps with specified label one. -/
def inclusion : Y.Etale ⥤ Object ρ where
  obj U := ⟨U⟩
  map f :=
    { label := 1
      left := f.left
      w := by
        rw [aut_one]
        simp }
  map_id _ := Object.Hom.ext rfl rfl
  map_comp _ _ := Object.Hom.ext (one_mul _).symm rfl

@[simp] theorem inclusion_map_label {U V : Y.Etale} (f : U ⟶ V) :
    ((inclusion ρ).map f).label = 1 := rfl

@[simp] theorem inclusion_map_left {U V : Y.Etale} (f : U ⟶ V) :
    ((inclusion ρ).map f).left = f.left := rfl

instance : (inclusion ρ).Faithful where
  map_injective h := MorphismProperty.Over.Hom.ext (congrArg Object.Hom.left h)

/-- Forget labels and structure maps, retaining the actual scheme map. -/
def toScheme : Object ρ ⥤ Scheme.{u} where
  obj U := U.etale.left
  map f := f.left

namespace Object

variable {ρ}

/-- Recover an ordinary small-etale map from a transport map labelled one. -/
def ordinaryMap {U V : Object ρ} (f : U ⟶ V) (h : f.label = 1) :
    U.etale ⟶ V.etale :=
  MorphismProperty.Over.homMk f.left (by simpa [h, aut_one] using f.w)

@[simp] theorem inclusion_ordinaryMap {U V : Object ρ} (f : U ⟶ V)
    (h : f.label = 1) : (inclusion ρ).map (ordinaryMap f h) = f :=
  Hom.ext h.symm rfl

/-- Translate the structure morphism by the automorphism attached to `g`. -/
def translate (g : G) (U : Object ρ) : Object ρ :=
  ⟨(EtaleAutomorphism.siteMap (aut ρ g)).obj U.etale⟩

@[simp] theorem translate_left (g : G) (U : Object ρ) :
    (translate g U).etale.left = U.etale.left := rfl

@[simp] theorem translate_hom (g : G) (U : Object ρ) :
    (translate g U).etale.hom = U.etale.hom ≫ (aut ρ g).hom := rfl

/-- Translation is an actual isomorphism in the group-labelled category. -/
def translationIso (g : G) (U : Object ρ) : U ≅ translate g U where
  hom :=
    { label := g
      left := 𝟙 _
      w := by simp }
  inv :=
    { label := g⁻¹
      left := 𝟙 _
      w := by
        simp only [Category.id_comp, translate_hom, Category.assoc]
        rw [← Iso.trans_hom, ← aut_mul, mul_inv_cancel, aut_one]
        simp }
  hom_inv_id := Hom.ext (mul_inv_cancel _) (Category.id_comp _)
  inv_hom_id := Hom.ext (inv_mul_cancel _) (Category.id_comp _)

@[simp] theorem translationIso_hom_label (g : G) (U : Object ρ) :
    (translationIso g U).hom.label = g := rfl

@[simp] theorem translationIso_hom_left (g : G) (U : Object ρ) :
    (translationIso g U).hom.left = 𝟙 U.etale.left := rfl

@[simp] theorem translationIso_inv_label (g : G) (U : Object ρ) :
    (translationIso g U).inv.label = g⁻¹ := rfl

@[simp] theorem translationIso_inv_left (g : G) (U : Object ρ) :
    (translationIso g U).inv.left = 𝟙 U.etale.left := rfl

/-- Every transport map becomes an ordinary etale map after translating its source. -/
def ordinaryPart {U V : Object ρ} (f : U ⟶ V) :
    (translate f.label U).etale ⟶ V.etale :=
  MorphismProperty.Over.homMk f.left f.w

@[simp] theorem ordinaryPart_left {U V : Object ρ} (f : U ⟶ V) :
    (ordinaryPart f).left = f.left := rfl

/-- The canonical factorization retains the actual scheme map and group label. -/
theorem translationIso_hom_comp_ordinaryPart {U V : Object ρ} (f : U ⟶ V) :
    (translationIso f.label U).hom ≫ (inclusion ρ).map (ordinaryPart f) = f :=
  Hom.ext (mul_one _) (Category.id_comp _)

/-- Undoing translation leaves the ordinary part of a transport map. -/
theorem translationIso_inv_comp {U V : Object ρ} (f : U ⟶ V) :
    (translationIso f.label U).inv ≫ f = (inclusion ρ).map (ordinaryPart f) :=
  Hom.ext (inv_mul_cancel _) (Category.id_comp _)

end Object

end Langlands.Geometry.EtaleTransport
