import Langlands.AlgebraicGeometry.CoherentSheaves.GeometricDescent
import Langlands.AlgebraicGeometry.Picard.LineBundleStackBase

/-! # The ordinary-module dictionary for categorical geometric descent -/

noncomputable section

universe u

open CategoryTheory Opposite Bicategory Limits AlgebraicGeometry
open CategoryTheory.Pseudofunctor CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat
open Langlands.Scheme.Modules Langlands.Scheme.Modules.LineBundleFlatDescent

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.AlgebraicGeometry.CoherentSheaves.ModuleDescentDictionary

/-- The core of the actual ordinary module pseudofunctor on schemes. -/
def pseudofunctor : LocallyDiscrete Scheme.{u}ᵒᵖ ⥤ᵖ Cat :=
  corePseudofunctor (Scheme.Modules.pseudofunctor.comp Adj.forget₁)

abbrev mod {X : Scheme.{u}} (M : pseudofunctor.obj (.mk (op X))) : X.Modules := M.of

abbrev modHom {X : Scheme.{u}} {M N : pseudofunctor.obj (.mk (op X))} (a : M ⟶ N) :
    mod M ⟶ mod N := a.iso.hom

@[simp]
lemma modHom_id {X : Scheme.{u}} (M : pseudofunctor.obj (.mk (op X))) :
    modHom (𝟙 M) = 𝟙 (mod M) := rfl

@[simp]
lemma modHom_comp {X : Scheme.{u}} {M N P : pseudofunctor.obj (.mk (op X))}
    (a : M ⟶ N) (b : N ⟶ P) : modHom (a ≫ b) = modHom a ≫ modHom b := rfl

@[simp]
lemma modHom_map {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : pseudofunctor.obj (.mk (op Y))} (a : M ⟶ N) :
    modHom ((pseudofunctor.map f.op.toLoc).toFunctor.map a) =
      (Scheme.Modules.pullback f).map (modHom a) := rfl

lemma modHom_mapComp'_hom {X Y Z : Scheme.{u}} (g : X ⟶ Y) (f : Y ⟶ Z)
    (gf : X ⟶ Z) (h : g ≫ f = gf)
    (hp : f.op.toLoc ≫ g.op.toLoc = gf.op.toLoc)
    (M : pseudofunctor.obj (.mk (op Z))) :
    modHom ((pseudofunctor.mapComp' f.op.toLoc g.op.toLoc gf.op.toLoc hp).hom.toNatTrans.app M) =
      (compIso g f gf h (mod M)).inv := by
  subst h
  rw [compIso_rfl]
  simp [Pseudofunctor.mapComp', pseudofunctor, corePseudofunctor,
    Scheme.Modules.pseudofunctor]

lemma modHom_mapComp'_inv {X Y Z : Scheme.{u}} (g : X ⟶ Y) (f : Y ⟶ Z)
    (gf : X ⟶ Z) (h : g ≫ f = gf)
    (hp : f.op.toLoc ≫ g.op.toLoc = gf.op.toLoc)
    (M : pseudofunctor.obj (.mk (op Z))) :
    modHom ((pseudofunctor.mapComp' f.op.toLoc g.op.toLoc gf.op.toLoc hp).inv.toNatTrans.app M) =
      (compIso g f gf h (mod M)).hom := by
  subst h
  rw [compIso_rfl]
  simp [Pseudofunctor.mapComp', pseudofunctor, corePseudofunctor,
    Scheme.Modules.pseudofunctor]

set_option maxHeartbeats 800000 in
lemma modHom_pullHom {Y X₁ X₂ Y' : Scheme.{u}}
    {M₁ : pseudofunctor.obj (.mk (op X₁))} {M₂ : pseudofunctor.obj (.mk (op X₂))}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (a : (pseudofunctor.map f₁.op.toLoc).toFunctor.obj M₁ ⟶
      (pseudofunctor.map f₂.op.toLoc).toFunctor.obj M₂)
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (h₁ : g ≫ f₁ = gf₁) (h₂ : g ≫ f₂ = gf₂) :
    modHom (pullHom a g gf₁ gf₂ h₁ h₂) = tr g h₁ h₂ (modHom a) := by
  simp only [pullHom, modHom_comp, modHom_mapComp'_hom g f₁ gf₁ h₁,
    modHom_mapComp'_inv g f₂ gf₂ h₂, modHom_map, tr]
  rfl

variable {X Y : Scheme.{u}} (p : X ⟶ Y)

lemma hom_congr (D : pseudofunctor.DescentData (fun _ : Unit ↦ p))
    {Z : Scheme.{u}} {q q' : Z ⟶ Y} (hq : q = q')
    (a b : Z ⟶ X) (ha : a ≫ p = q) (hb : b ≫ p = q) :
    D.hom q (i₁ := ()) (i₂ := ()) a b ha hb =
      D.hom q' (i₁ := ()) (i₂ := ()) a b (ha.trans hq) (hb.trans hq) := by
  subst hq
  rfl

/-- Full categorical descent data give an all-scheme-test geometric datum on the
actual ordinary module of the cover object. -/
def datum (D : pseudofunctor.DescentData (fun _ : Unit ↦ p)) :
    Datum p (mod (D.obj ())) where
  θ U a b h := (D.hom (a ≫ p) (i₁ := ()) (i₂ := ()) a b rfl h.symm).iso
  nat U V k a b h h' := by
    have h₂ := congrArg modHom (D.pullHom_hom k (a ≫ p) ((k ≫ a) ≫ p) (by simp)
      (i₁ := ()) (i₂ := ()) a b rfl h.symm (k ≫ a) (k ≫ b) rfl rfl)
    rw [modHom_pullHom] at h₂
    change modHom _ = _
    rw [← h₂, tr, compIso_rfl, compIso_rfl]
    rfl
  coc U a b c h h' h'' := by
    change modHom _ ≫ modHom _ = modHom _
    rw [← modHom_comp, hom_congr p D h.symm b c rfl h'.symm, D.hom_comp]


set_option maxHeartbeats 1600000 in
lemma modHom_toDescentData_obj_hom {B : Scheme.{u}} {ι : Type*} {Z : ι → Scheme.{u}}
    (f : ∀ i, Z i ⟶ B) (M : pseudofunctor.obj (.mk (op B)))
    {V : Scheme.{u}} (q : V ⟶ B) {i₁ i₂ : ι}
    (f₁ : V ⟶ Z i₁) (f₂ : V ⟶ Z i₂)
    (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    modHom (((pseudofunctor.toDescentData f).obj M).hom q f₁ f₂ hf₁ hf₂) =
      (compIso f₁ (f i₁) q hf₁ (mod M)).hom ≫
        (compIso f₂ (f i₂) q hf₂ (mod M)).inv := by
  change modHom ((Pseudofunctor.DescentData.ofObj (f := f) M).hom q f₁ f₂ hf₁ hf₂) = _
  simp only [Pseudofunctor.DescentData.ofObj_hom, modHom_comp,
    modHom_mapComp'_inv f₁ (f i₁) q hf₁, modHom_mapComp'_hom f₂ (f i₂) q hf₂]

lemma datum_θ_hom (D : pseudofunctor.DescentData (fun _ : Unit ↦ p))
    {V : Scheme.{u}} (a b : V ⟶ X) (h : a ≫ p = b ≫ p) :
    ((datum p D).θ V a b h).hom =
      modHom (D.hom (a ≫ p) (i₁ := ()) (i₂ := ()) a b rfl h.symm) := rfl

set_option maxHeartbeats 1600000 in
/-- An effective geometric structure gives an isomorphism to the full categorical
singleton descent datum, with compatibility on every scheme test. -/
def effectiveIso (D : pseudofunctor.DescentData (fun _ : Unit ↦ p))
    (M : Y.Modules) (S : Str (datum p D) (𝟙 Y) M) :
    (pseudofunctor.toDescentData (fun _ : Unit ↦ p)).obj ⟨M⟩ ≅ D := by
  let F₀ := mod (D.obj ())
  have hs₀ : p ≫ 𝟙 Y = 𝟙 X ≫ p := by simp
  let γ₀ := S.γ X (𝟙 X) p hs₀
  let E : (Scheme.Modules.pullback p).obj M ≅ F₀ :=
    γ₀ ≪≫ (Scheme.Modules.pullbackId X).app F₀
  have n (Y' : Scheme.{u}) (f' : Y' ⟶ X) (q : Y' ⟶ Y) (hf' : f' ≫ p = q) :
      (Scheme.Modules.pullback f').map γ₀.hom =
        (compIso f' p q hf' M).hom ≫
          (S.γ Y' f' q (by rw [Category.comp_id, hf'])).hom ≫
          (compIso f' (𝟙 X) f' (Category.comp_id f') F₀).inv := by
    rw [S.nat X Y' f' (𝟙 X) p hs₀ f' q (by rw [Category.comp_id, hf'])
      (Category.comp_id f') hf', tr]
    simp
    rfl
  refine Pseudofunctor.DescentData.isoMk (fun _ ↦ Core.isoMk E) ?_
  rintro Y' q ⟨⟩ ⟨⟩ f₁ f₂ hf₁ hf₂
  apply Core.hom_ext
  change modHom _ = modHom _
  rw [modHom_comp, modHom_comp, modHom_map, modHom_map,
    modHom_toDescentData_obj_hom (fun _ : Unit ↦ p) ⟨M⟩ q f₁ f₂ hf₁ hf₂,
    hom_congr p D hf₁.symm f₁ f₂ hf₁ hf₂,
    ← datum_θ_hom p D f₁ f₂ (hf₁.trans hf₂.symm)]
  change (Scheme.Modules.pullback f₁).map E.hom ≫ _ =
    _ ≫ (Scheme.Modules.pullback f₂).map E.hom
  simp only [E, Iso.trans_hom, Iso.app_hom, Functor.map_comp, Category.assoc]
  rw [n Y' f₁ q hf₁, n Y' f₂ q hf₂,
    Picard.map_pullbackId_hom_app, Picard.map_pullbackId_hom_app]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  rw [S.coc Y' f₁ f₂ q (by rw [Category.comp_id, hf₁])
    (by rw [Category.comp_id, hf₂]) (hf₁.trans hf₂.symm)]

/-- Quasi-coherent categorical singleton data along an affine flat surjection
are effective in the core of actual ordinary modules. -/
lemma exists_effective [IsAffineHom p] [Flat p] [Surjective p]
    (D : pseudofunctor.DescentData (fun _ : Unit ↦ p))
    [(mod (D.obj ())).IsQuasicoherent] :
    ∃ M : Y.Modules, M.IsQuasicoherent ∧
      Nonempty ((pseudofunctor.toDescentData (fun _ : Unit ↦ p)).obj ⟨M⟩ ≅ D) := by
  obtain ⟨M, hM, ⟨S⟩⟩ := Modules.GeometricQuasicoherentDescent.exists_str (datum p D) (𝟙 Y)
  exact ⟨M, hM, ⟨effectiveIso p D M S⟩⟩

end Langlands.AlgebraicGeometry.CoherentSheaves.ModuleDescentDictionary
