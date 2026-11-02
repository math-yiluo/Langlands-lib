import Langlands.AlgebraicGeometry.Picard.Groupoid
import Langlands.AlgebraicGeometry.Modules.LineBundleFlatDescentStr
import Mathlib.CategoryTheory.Sites.Descent.DescentData

/-! # Module realizations of pseudofunctors of line bundles -/

universe u

open CategoryTheory Opposite Bicategory AlgebraicGeometry
open CategoryTheory.Pseudofunctor CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat
open Langlands.Scheme.Modules Langlands.Scheme.Modules.LineBundleFlatDescent

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

/-- A realization of a pseudofunctor on schemes by line bundles: objects have underlying
locally free modules of rank one, morphisms are the isomorphisms of underlying modules, and
pullbacks and their composition comparisons are the module ones, up to chosen
identifications `mapIso`. -/
structure ModuleRealization (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat.{u, u + 1}) where
  /-- The underlying module. -/
  mod {X : Scheme.{u}} : F.obj (.mk (op X)) → X.Modules
  /-- The underlying module morphism. -/
  modHom {X : Scheme.{u}} {M N : F.obj (.mk (op X))} : (M ⟶ N) → (mod M ⟶ mod N)
  modHom_comp {X : Scheme.{u}} {M N P : F.obj (.mk (op X))} (φ : M ⟶ N) (ψ : N ⟶ P) :
    modHom (φ ≫ ψ) = modHom φ ≫ modHom ψ
  modHom_id {X : Scheme.{u}} (M : F.obj (.mk (op X))) : modHom (𝟙 M) = 𝟙 (mod M)
  modHom_injective {X : Scheme.{u}} {M N : F.obj (.mk (op X))} :
    Function.Injective (modHom (M := M) (N := N))
  isIso_modHom {X : Scheme.{u}} {M N : F.obj (.mk (op X))} (φ : M ⟶ N) : IsIso (modHom φ)
  /-- Module isomorphisms are morphisms. -/
  ofIso {X : Scheme.{u}} {M N : F.obj (.mk (op X))} : (mod M ≅ mod N) → (M ⟶ N)
  modHom_ofIso {X : Scheme.{u}} {M N : F.obj (.mk (op X))} (e : mod M ≅ mod N) :
    modHom (ofIso e) = e.hom
  rankOne {X : Scheme.{u}} (M : F.obj (.mk (op X))) : IsLocallyFreeRankOne (mod M)
  /-- Every line bundle underlies an object. -/
  ofModule {X : Scheme.{u}} (L : X.Modules) (hL : IsLocallyFreeRankOne L) : F.obj (.mk (op X))
  /-- The identification of the module underlying `ofModule L`. -/
  ofModuleIso {X : Scheme.{u}} (L : X.Modules) (hL : IsLocallyFreeRankOne L) :
    mod (ofModule L hL) ≅ L
  /-- The identification of the module underlying a pullback. -/
  mapIso {X Y : Scheme.{u}} (f : X ⟶ Y) (M : F.obj (.mk (op Y))) :
    mod ((F.map f.op.toLoc).toFunctor.obj M) ≅ (Scheme.Modules.pullback f).obj (mod M)
  modHom_map {X Y : Scheme.{u}} (f : X ⟶ Y) {M N : F.obj (.mk (op Y))} (φ : M ⟶ N) :
    modHom ((F.map f.op.toLoc).toFunctor.map φ) =
      (mapIso f M).hom ≫ (Scheme.Modules.pullback f).map (modHom φ) ≫ (mapIso f N).inv
  modHom_mapComp'_hom {X Y Z : Scheme.{u}} (g : X ⟶ Y) (u : Y ⟶ Z) (u' : X ⟶ Z)
    (h : g ≫ u = u') (hp : u.op.toLoc ≫ g.op.toLoc = u'.op.toLoc) (M : F.obj (.mk (op Z))) :
    modHom ((F.mapComp' u.op.toLoc g.op.toLoc u'.op.toLoc hp).hom.toNatTrans.app M) =
      (mapIso u' M).hom ≫ (compIso g u u' h (mod M)).inv ≫
        (Scheme.Modules.pullback g).map (mapIso u M).inv ≫ (mapIso g _).inv

namespace ModuleRealization

variable {F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat.{u, u + 1}} (R : ModuleRealization F)

attribute [simp] modHom_comp modHom_id modHom_ofIso

attribute [instance] isIso_modHom

/-- The module isomorphism underlying a morphism. -/
def modIso {X : Scheme.{u}} {M N : F.obj (.mk (op X))} (φ : M ⟶ N) : R.mod M ≅ R.mod N :=
  asIso (R.modHom φ)

@[simp]
lemma modIso_hom {X : Scheme.{u}} {M N : F.obj (.mk (op X))} (φ : M ⟶ N) :
    (R.modIso φ).hom = R.modHom φ :=
  rfl

lemma hom_ext {X : Scheme.{u}} {M N : F.obj (.mk (op X))} {φ ψ : M ⟶ N}
    (h : R.modHom φ = R.modHom ψ) : φ = ψ :=
  R.modHom_injective h

lemma modHom_mapComp'_inv {X Y Z : Scheme.{u}} (g : X ⟶ Y) (u : Y ⟶ Z) (u' : X ⟶ Z)
    (h : g ≫ u = u') (hp : u.op.toLoc ≫ g.op.toLoc = u'.op.toLoc) (M : F.obj (.mk (op Z))) :
    R.modHom ((F.mapComp' u.op.toLoc g.op.toLoc u'.op.toLoc hp).inv.toNatTrans.app M) =
      (R.mapIso g _).hom ≫ (Scheme.Modules.pullback g).map (R.mapIso u M).hom ≫
        (compIso g u u' h (R.mod M)).hom ≫ (R.mapIso u' M).inv := by
  let I := R.mapIso u' M ≪≫ (compIso g u u' h (R.mod M)).symm ≪≫
    (Scheme.Modules.pullback g).mapIso (R.mapIso u M).symm ≪≫ (R.mapIso g _).symm
  have hI : R.modHom ((F.mapComp' u.op.toLoc g.op.toLoc u'.op.toLoc hp).hom.toNatTrans.app M) =
      I.hom := by
    rw [R.modHom_mapComp'_hom g u u' h hp M]
    rfl
  rw [← cancel_mono I.hom]
  conv_lhs => rw [← hI]
  rw [← R.modHom_comp, Cat.Hom.inv_hom_id_toNatTrans_app, R.modHom_id]
  simp [I, Iso.map_hom_inv_id_assoc]

/-- The module form of a morphism between pullbacks. -/
def μ {Y X₁ X₂ : Scheme.{u}} {M₁ : F.obj (.mk (op X₁))} {M₂ : F.obj (.mk (op X₂))}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂) :
    (Scheme.Modules.pullback f₁).obj (R.mod M₁) ⟶ (Scheme.Modules.pullback f₂).obj (R.mod M₂) :=
  (R.mapIso f₁ M₁).inv ≫ R.modHom φ ≫ (R.mapIso f₂ M₂).hom

section μ

variable {Y X₁ X₂ X₃ : Scheme.{u}} {M₁ : F.obj (.mk (op X₁))} {M₂ : F.obj (.mk (op X₂))}
  {M₃ : F.obj (.mk (op X₃))} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂} {f₃ : Y ⟶ X₃}

@[reassoc]
lemma μ_comp
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (ψ : (F.map f₂.op.toLoc).toFunctor.obj M₂ ⟶ (F.map f₃.op.toLoc).toFunctor.obj M₃) :
    R.μ (φ ≫ ψ) = R.μ φ ≫ R.μ ψ := by
  simp [μ]

lemma μ_id : R.μ (𝟙 ((F.map f₁.op.toLoc).toFunctor.obj M₁)) = 𝟙 _ := by
  simp [μ]

lemma μ_injective
    {φ ψ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂}
    (h : R.μ φ = R.μ ψ) : φ = ψ := by
  apply R.hom_ext
  simpa [μ, cancel_epi, cancel_mono] using h

/-- The module form of an isomorphism. -/
def μIso
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂) :
    (Scheme.Modules.pullback f₁).obj (R.mod M₁) ≅ (Scheme.Modules.pullback f₂).obj (R.mod M₂) :=
  (R.mapIso f₁ M₁).symm ≪≫ R.modIso φ ≪≫ R.mapIso f₂ M₂

@[simp]
lemma μIso_hom
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂) :
    (R.μIso φ).hom = R.μ φ :=
  rfl

lemma μ_map {X : Scheme.{u}} (f : Y ⟶ X) {M N : F.obj (.mk (op X))} (φ : M ⟶ N) :
    R.μ ((F.map f.op.toLoc).toFunctor.map φ) = (Scheme.Modules.pullback f).map (R.modHom φ) := by
  simp [μ, R.modHom_map]

lemma μ_pullHom
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂)
    {Y' : Scheme.{u}} (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (h₁ : g ≫ f₁ = gf₁)
    (h₂ : g ≫ f₂ = gf₂) :
    R.μ (pullHom φ g gf₁ gf₂ h₁ h₂) = tr g h₁ h₂ (R.μ φ) := by
  simp only [μ, pullHom, R.modHom_comp, R.modHom_mapComp'_hom g f₁ gf₁ h₁,
    R.modHom_mapComp'_inv g f₂ gf₂ h₂, R.modHom_map, tr, Functor.map_comp, Category.assoc,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

end μ

lemma μ_ofObj_hom {S : Scheme.{u}} {ι : Type*} {X : ι → Scheme.{u}} {f : ∀ i, X i ⟶ S}
    (M : F.obj (.mk (op S))) {Y : Scheme.{u}} (q : Y ⟶ S) {i₁ i₂ : ι}
    (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    R.μ ((Pseudofunctor.DescentData.ofObj (f := f) M).hom q f₁ f₂ hf₁ hf₂) =
      (Scheme.Modules.pullback f₁).map (R.mapIso (f i₁) M).hom ≫
        (compIso f₁ (f i₁) q hf₁ (R.mod M)).hom ≫ (compIso f₂ (f i₂) q hf₂ (R.mod M)).inv ≫
          (Scheme.Modules.pullback f₂).map (R.mapIso (f i₂) M).inv := by
  simp only [μ, Pseudofunctor.DescentData.ofObj_hom, R.modHom_comp,
    R.modHom_mapComp'_inv f₁ (f i₁) q hf₁, R.modHom_mapComp'_hom f₂ (f i₂) q hf₂,
    Category.assoc]
  erw [Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  simp only [Iso.inv_hom_id_assoc]

lemma μ_toDescentData_obj_hom {S : Scheme.{u}} {ι : Type*} {X : ι → Scheme.{u}}
    (f : ∀ i, X i ⟶ S) (M : F.obj (.mk (op S))) {Y : Scheme.{u}} (q : Y ⟶ S) {i₁ i₂ : ι}
    (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    R.μ (((F.toDescentData f).obj M).hom q f₁ f₂ hf₁ hf₂) =
      (Scheme.Modules.pullback f₁).map (R.mapIso (f i₁) M).hom ≫
        (compIso f₁ (f i₁) q hf₁ (R.mod M)).hom ≫ (compIso f₂ (f i₂) q hf₂ (R.mod M)).inv ≫
          (Scheme.Modules.pullback f₂).map (R.mapIso (f i₂) M).inv :=
  R.μ_ofObj_hom M q f₁ f₂ hf₁ hf₂

end ModuleRealization

namespace PicardGroupoid

/-- The underlying module sheaf of an object of the line-bundle pseudofunctor. -/
abbrev mod {X : Scheme.{u}} (M : pseudofunctor.{u}.obj (.mk (op X))) : X.Modules := M.of.obj

/-- The underlying module morphism of a morphism of the line-bundle pseudofunctor. -/
abbrev modHom {X : Scheme.{u}} {M N : pseudofunctor.{u}.obj (.mk (op X))} (φ : M ⟶ N) :
    mod M ⟶ mod N :=
  φ.iso.hom.hom

variable {X Y Z : Scheme.{u}}

lemma modHom_mapComp'_hom (g : X ⟶ Y) (u : Y ⟶ Z) (u' : X ⟶ Z) (h : g ≫ u = u')
    (hp : u.op.toLoc ≫ g.op.toLoc = u'.op.toLoc) (M : pseudofunctor.{u}.obj (.mk (op Z))) :
    modHom ((pseudofunctor.{u}.mapComp' u.op.toLoc g.op.toLoc u'.op.toLoc
      hp).hom.toNatTrans.app M) = (compIso g u u' h (mod M)).inv := by
  subst h
  rw [compIso_rfl]
  simp [Pseudofunctor.mapComp', pseudofunctor, PicardGroupoid.pullbackComp,
    LineBundle.pullbackComp]
  exact Category.id_comp _

/-- The line-bundle pseudofunctor is realized by its underlying modules, with identity
identifications of pullbacks. -/
def moduleRealization : ModuleRealization pseudofunctor.{u} where
  mod M := mod M
  modHom φ := modHom φ
  modHom_comp _ _ := rfl
  modHom_id _ := rfl
  modHom_injective {_ _ _} φ ψ h := by
    apply Core.hom_ext
    exact ObjectProperty.hom_ext _ h
  isIso_modHom φ := (Iso.isIso_hom ((ObjectProperty.ι _).mapIso φ.iso) :)
  ofIso e := ⟨ObjectProperty.isoMk _ e⟩
  modHom_ofIso _ := rfl
  rankOne M := M.of.property
  ofModule L hL := ⟨⟨L, hL⟩⟩
  ofModuleIso _ _ := Iso.refl _
  mapIso _ _ := Iso.refl _
  modHom_map f M N φ := by
    simp only [Iso.refl_hom, Iso.refl_inv, Category.id_comp]
    exact (Category.comp_id _).symm
  modHom_mapComp'_hom g u u' h hp M := by
    rw [modHom_mapComp'_hom g u u' h hp M]
    simp only [Iso.refl_hom, Iso.refl_inv, Category.id_comp]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]

end PicardGroupoid

end Langlands.AlgebraicGeometry.Picard
