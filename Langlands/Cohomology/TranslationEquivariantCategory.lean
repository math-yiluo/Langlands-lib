import Langlands.Cohomology.TranslationAction

/-!
# Morphisms of translation-equivariant objects
-/

noncomputable section

namespace Langlands.Cohomology.TranslationAction.Equivariant

open CategoryTheory

universe v u v' u' w

variable {C : Type u} [Category.{v} C]
variable {D : Type u'} [Category.{v'} D]
variable {Γ : C ⥤ D} {G : Type w} [Monoid G] {T : G → C ⥤ C}
variable {𝒯 : Data Γ T}

/-- A morphism commuting with every translation structure map. -/
@[ext] structure Hom (F E : Equivariant 𝒯) where
  hom : F.obj ⟶ E.obj
  comm (g : G) : F.act g ≫ hom = (T g).map hom ≫ E.act g

/-- Identity on the underlying object. -/
def Hom.id (F : Equivariant 𝒯) : Hom F F where
  hom := 𝟙 F.obj
  comm g := by simp

/-- Underlying composition preserves equivariance. -/
def Hom.comp {F E K : Equivariant 𝒯} (f : Hom F E) (h : Hom E K) : Hom F K where
  hom := f.hom ≫ h.hom
  comm g := by
    rw [← Category.assoc, f.comm, Category.assoc, h.comm]
    simp only [Functor.map_comp, Category.assoc]

instance : Category (Equivariant 𝒯) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp f := by ext; simp [Hom.id, Hom.comp]
  comp_id f := by ext; simp [Hom.id, Hom.comp]
  assoc f h k := by ext; simp [Hom.comp, Category.assoc]

@[simp] theorem id_hom (F : Equivariant 𝒯) :
    (𝟙 F : F ⟶ F).hom = 𝟙 F.obj := rfl

@[simp] theorem comp_hom {F E K : Equivariant 𝒯} (f : F ⟶ E) (h : E ⟶ K) :
    (f ≫ h).hom = f.hom ≫ h.hom := rfl

/-- Forget the translation structure and retain the underlying object. -/
def forget : Equivariant 𝒯 ⥤ C where
  obj F := F.obj
  map f := f.hom

instance : (forget (𝒯 := 𝒯)).Faithful where
  map_injective h := Hom.ext h

/-- An equivariant underlying isomorphism is an isomorphism of equivariant
objects; equivariance of its inverse follows from that of its forward map. -/
def mkIso {F E : Equivariant 𝒯} (e : F.obj ≅ E.obj)
    (comm : ∀ g, F.act g ≫ e.hom = (T g).map e.hom ≫ E.act g) : F ≅ E where
  hom := ⟨e.hom, comm⟩
  inv :=
    { hom := e.inv
      comm g := by
        apply (cancel_mono e.hom).1
        simp only [Category.assoc, e.inv_hom_id, Category.comp_id]
        rw [comm]
        rw [← (T g).map_comp_assoc, e.inv_hom_id, (T g).map_id, Category.id_comp] }
  hom_inv_id := Hom.ext e.hom_inv_id
  inv_hom_id := Hom.ext e.inv_hom_id

@[simp] theorem mkIso_hom_hom {F E : Equivariant 𝒯} (e : F.obj ≅ E.obj)
    (comm : ∀ g, F.act g ≫ e.hom = (T g).map e.hom ≫ E.act g) :
    (mkIso e comm).hom.hom = e.hom := rfl

@[simp] theorem mkIso_inv_hom {F E : Equivariant 𝒯} (e : F.obj ≅ E.obj)
    (comm : ∀ g, F.act g ≫ e.hom = (T g).map e.hom ≫ E.act g) :
    (mkIso e comm).inv.hom = e.inv := rfl

end Langlands.Cohomology.TranslationAction.Equivariant
