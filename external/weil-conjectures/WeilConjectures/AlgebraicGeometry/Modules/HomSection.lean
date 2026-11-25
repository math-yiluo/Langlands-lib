/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs

/-!
# The section attached to a trivialisation of a pullback

A morphism `φ : f^* 𝒪_X ⟶ f^* A` is determined by the section `φ(f^* 1)` of `f^* A`
(`AlgebraicGeometry.Scheme.Modules.homSection`). Under restriction along `g`, this section is
pulled back (`AlgebraicGeometry.Scheme.Modules.homSection_comp`), and a free generator `e` of
`A` gives a trivialisation whose attached section is the pullback of `e`
(`AlgebraicGeometry.Scheme.Modules.exists_isIso_homSection_eq`). The transition functions of
generators pull back to those of the attached sections
(`AlgebraicGeometry.Scheme.Modules.genSection_eq_smul`).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y Z : Scheme.{u}}

lemma pullbackSection_pullbackSection (f : X ⟶ Y) (g : Y ⟶ Z)
    {M : Z.Modules} {U : Z.Opens} (m : Γ(M, U)) :
    pullbackSection f (pullbackSection g m) =
      ((pullbackComp f g).inv.app M).app ((f ≫ g) ⁻¹ᵁ U) (pullbackSection (f ≫ g) m) := by
  have h := unit_conjugateEquiv
    ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f))
    (pullbackPushforwardAdjunction (f ≫ g)) (pullbackComp f g).inv M
  rw [conjugateEquiv_pullbackComp_inv] at h
  have h' := congr_arg (fun φ ↦ (Hom.app φ U) m) h
  simp only at h'
  exact h'

/-- The section `φ(1)` of `f^* A` attached to `φ : f^* 𝒪 ⟶ f^* A`. -/
noncomputable def homSection (f : Y ⟶ X) {A : X.Modules}
    (φ : (pullback f).obj (unit X) ⟶ (pullback f).obj A) : Γ((pullback f).obj A, f ⁻¹ᵁ ⊤) :=
  φ.app (f ⁻¹ᵁ ⊤) (pullbackSection f (1 : Γ(X, ⊤)))

lemma homSection_comp (f : Y ⟶ X) (g : Z ⟶ Y) {A : X.Modules}
    (φ : (pullback f).obj (unit X) ⟶ (pullback f).obj A) :
    homSection (g ≫ f) ((pullbackComp g f).inv.app _ ≫ (pullback g).map φ ≫
        (pullbackComp g f).hom.app A) =
      ((pullbackComp g f).hom.app A).app _ (pullbackSection g (homSection f φ)) := by
  have h1 := pullbackSection_pullbackSection g f (M := unit X) (1 : Γ(X, ⊤))
  have h2 := congrArg (fun ψ ↦ Hom.app ψ (f ⁻¹ᵁ ⊤) (pullbackSection f (M := unit X) (1 : Γ(X, ⊤))))
    ((pullbackPushforwardAdjunction g).unit.naturality φ)
  simp only [Functor.id_map, Functor.comp_map, Hom.comp_app, pushforward_map_app,
    ConcreteCategory.comp_apply] at h2
  simp only [homSection, Hom.comp_app, ConcreteCategory.comp_apply]
  rw [← h1]
  exact congrArg _ h2.symm

lemma homSection_smulHom_comp (f : Y ⟶ X) {A : X.Modules} (c : Γ(Y, ⊤))
    (φ : (pullback f).obj (unit X) ⟶ (pullback f).obj A) :
    homSection f (Modules.smulHom ((pullback f).obj (unit X)) c ≫ φ) =
      Y.presheaf.map (homOfLE (le_top (a := f ⁻¹ᵁ ⊤))).op c • homSection f φ := by
  simp only [homSection, Hom.comp_app, ConcreteCategory.comp_apply, smulHom_app_apply]
  exact Hom.app_smul _ _ _

lemma unit_hom_ext {N : Y.Modules} {ψ₁ ψ₂ : unit Y ⟶ N}
    (h : ψ₁.app ⊤ (1 : Γ(Y, ⊤)) = ψ₂.app ⊤ (1 : Γ(Y, ⊤))) : ψ₁ = ψ₂ := by
  ext U x
  let x' : Γ(Y, U) := x
  have e (ψ : unit Y ⟶ N) : ψ.app U x =
      x' • N.presheaf.map (homOfLE (le_top (a := U))).op (ψ.app ⊤ (1 : Γ(Y, ⊤))) := by
    have h₁ : ψ.app U x = x' • ψ.app U (show Γ(unit Y, U) from (1 : Γ(Y, U))) := by
      rw [← Hom.app_smul]
      congr 1
      exact (mul_one x').symm
    have h₂ : ψ.app U (show Γ(unit Y, U) from (1 : Γ(Y, U))) =
        N.presheaf.map (homOfLE (le_top (a := U))).op
          (ψ.app ⊤ (show Γ(unit Y, ⊤) from (1 : Γ(Y, ⊤)))) := by
      rw [← Hom.app_presheaf_map]
      congr 1
      exact (map_one (Y.presheaf.map (homOfLE (le_top (a := U))).op).hom).symm
    rw [h₁, h₂]
  rw [e ψ₁, e ψ₂, h]

lemma homSection_injective (f : Y ⟶ X) {A : X.Modules} :
    Function.Injective (homSection f (A := A)) := by
  intro φ ψ h
  have e1 : pullbackSection f (M := unit X) (1 : Γ(X, ⊤)) =
      Hom.app (pullbackObjUnitIso f).inv (f ⁻¹ᵁ ⊤) (1 : Γ(Y, ⊤)) := by
    have := pullbackSection_app_one f (𝟙 (unit X))
    erw [CategoryTheory.Functor.map_id, Category.comp_id] at this
    exact this
  have key : (pullbackObjUnitIso f).inv ≫ φ = (pullbackObjUnitIso f).inv ≫ ψ := by
    apply unit_hom_ext
    simp only [homSection, e1] at h
    simp only [Hom.comp_app]
    exact h
  have := congrArg ((pullbackObjUnitIso f).hom ≫ ·) key
  erw [Iso.hom_inv_id_assoc, Iso.hom_inv_id_assoc] at this
  exact this

open Pseudofunctor.LocallyDiscreteOpToCat in
set_option backward.isDefEq.respectTransparency.types false in
lemma pullHom_eq_pullbackComp (f : Y ⟶ X) (g : Z ⟶ Y) {B A : modulesPseudofunctor.obj (.mk (op X))}
    (φ : (modulesPseudofunctor.map f.op.toLoc).toFunctor.obj B ⟶
      (modulesPseudofunctor.map f.op.toLoc).toFunctor.obj A) :
    pullHom (F := modulesPseudofunctor) φ g (g ≫ f) (g ≫ f) rfl rfl =
      (pullbackComp g f).inv.app (B : X.Modules) ≫ (pullback g).map φ ≫
        (pullbackComp g f).hom.app (A : X.Modules) := by
  dsimp only [pullHom]
  erw [Pseudofunctor.mapComp'_eq_mapComp]
  rfl

/-- The pullback along `f` of a section `e` over `U`, restricted to `f⁻¹ ⊤` when `f⁻¹ U = ⊤`. -/
noncomputable def genSection (f : Y ⟶ X) {A : X.Modules} {U : X.Opens} (e : Γ(A, U))
    (hU : f ⁻¹ᵁ U = ⊤) : Γ((pullback f).obj A, f ⁻¹ᵁ ⊤) :=
  ((pullback f).obj A).presheaf.map (homOfLE (by rw [hU]; exact le_top)).op (pullbackSection f e)

lemma pullbackComp_hom_inv_res (g : Z ⟶ Y) (f : Y ⟶ X) {A : X.Modules} {V W : Z.Opens}
    (i : V ⟶ W) (x : Γ((pullback (g ≫ f)).obj A, W)) :
    ((pullbackComp g f).hom.app A).app V
        (((pullback g).obj ((pullback f).obj A)).presheaf.map i.op
          (((pullbackComp g f).inv.app A).app W x)) =
      ((pullback (g ≫ f)).obj A).presheaf.map i.op x := by
  have e : ((pullbackComp g f).hom.app A).app W (((pullbackComp g f).inv.app A).app W x) = x := by
    rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, Iso.inv_hom_id_app, Hom.id_app]
    rfl
  exact (Hom.app_presheaf_map ((pullbackComp g f).hom.app A) i _).trans (congrArg _ e)

open Pseudofunctor.LocallyDiscreteOpToCat in
set_option backward.isDefEq.respectTransparency.types false in
lemma homSection_pullHom (f : Y ⟶ X) (g : Z ⟶ Y) (gf : Z ⟶ X) (h : g ≫ f = gf)
    {A : modulesPseudofunctor.obj (.mk (op X))} {U : X.Opens} (e : Γ((A : X.Modules), U))
    (hU : f ⁻¹ᵁ U = ⊤) (hU' : gf ⁻¹ᵁ U = ⊤)
    (φ : (modulesPseudofunctor.map f.op.toLoc).toFunctor.obj (unit X : X.Modules) ⟶
      (modulesPseudofunctor.map f.op.toLoc).toFunctor.obj A)
    (hφ : homSection f φ = genSection f e hU) :
    homSection gf (pullHom (F := modulesPseudofunctor) φ g gf gf h h) = genSection gf e hU' := by
  subst h
  rw [pullHom_eq_pullbackComp]
  refine (homSection_comp f g (A := (A : X.Modules)) φ).trans ?_
  rw [hφ, genSection, pullbackSection_map, pullbackSection_pullbackSection, genSection]
  exact pullbackComp_hom_inv_res g f (A := (A : X.Modules)) _ _

lemma pullbackSection_one_eq (f : Y ⟶ X) :
    pullbackSection f (M := unit X) (1 : Γ(X, ⊤)) =
      Hom.app (pullbackObjUnitIso f).inv (f ⁻¹ᵁ ⊤) (1 : Γ(Y, ⊤)) := by
  have := pullbackSection_app_one f (𝟙 (unit X))
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at this
  exact this

set_option backward.isDefEq.respectTransparency.types false in
/-- **A free generator trivialises the pullback**, with prescribed attached section. -/
lemma exists_isIso_homSection_eq (f : Y ⟶ X) {A : X.Modules} {U : X.Opens} {e : Γ(A, U)}
    (he : IsFreeGenerator e) (hU : f ⁻¹ᵁ U = ⊤) :
    ∃ φ : (pullback f).obj (unit X) ⟶ (pullback f).obj A, IsIso φ ∧
      homSection f φ = genSection f e hU := by
  have hs : IsFreeGenerator (genSection f e hU) := (he.pullback_unit_app f).map _
  have := isIso_homOfGlobalSection hs
  refine ⟨(pullbackObjUnitIso f).hom ≫ homOfGlobalSection _ (genSection f e hU),
    inferInstance, ?_⟩
  have k : (pullbackObjUnitIso f).hom.app ⊤
      ((pullbackObjUnitIso f).inv.app ⊤ (1 : Γ(Y, ⊤))) = (1 : Γ(Y, ⊤)) := by
    rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, Iso.inv_hom_id, Hom.id_app]
    rfl
  rw [homSection, pullbackSection_one_eq]
  change (homOfGlobalSection _ _).app ⊤ ((pullbackObjUnitIso f).hom.app ⊤
      ((pullbackObjUnitIso f).inv.app ⊤ (1 : Γ(Y, ⊤)))) = _
  rw [k, homOfGlobalSection_app_one]
  exact congrArg (fun φ : Γ((pullback f).obj A, ⊤) ⟶ Γ((pullback f).obj A, ⊤) ↦ φ _)
    (((pullback f).obj A).presheaf.map_id _)

lemma preimage_inf_eq_top (f : Y ⟶ X) {U₁ U₂ : X.Opens} (h₁ : f ⁻¹ᵁ U₁ = ⊤)
    (h₂ : f ⁻¹ᵁ U₂ = ⊤) : f ⁻¹ᵁ (U₁ ⊓ U₂) = ⊤ := by
  rw [Scheme.Hom.preimage_inf, h₁, h₂, inf_idem]

/-- **Transition functions of generators pull back.** If `e₂ = c • e₁` on `U₁ ⊓ U₂`, then the
attached sections over `Y` differ by the pullback of `c`. -/
lemma genSection_eq_smul (f : Y ⟶ X) {A : X.Modules} {U₁ U₂ : X.Opens} (e₁ : Γ(A, U₁))
    (e₂ : Γ(A, U₂)) (c : Γ(X, U₁ ⊓ U₂))
    (h : A.presheaf.map (homOfLE inf_le_right).op e₂ =
      c • A.presheaf.map (homOfLE inf_le_left).op e₁)
    (h₁ : f ⁻¹ᵁ U₁ = ⊤) (h₂ : f ⁻¹ᵁ U₂ = ⊤) :
    genSection f e₂ h₂ = Y.presheaf.map (homOfLE (by
        rw [preimage_inf_eq_top f h₁ h₂]; exact le_top) :
          f ⁻¹ᵁ ⊤ ⟶ f ⁻¹ᵁ (U₁ ⊓ U₂)).op (f.app _ c) • genSection f e₁ h₁ := by
  have htop : f ⁻¹ᵁ ⊤ ≤ f ⁻¹ᵁ (U₁ ⊓ U₂) := by
    rw [preimage_inf_eq_top f h₁ h₂]; exact le_top
  have r (U : X.Opens) (hU : f ⁻¹ᵁ U = ⊤) (hle : U₁ ⊓ U₂ ≤ U) (e : Γ(A, U)) :
      genSection f e hU = ((pullback f).obj A).presheaf.map (homOfLE htop).op
        (((pullback f).obj A).presheaf.map (homOfLE (f.preimage_mono hle)).op
          (pullbackSection f e)) := by
    rw [genSection, presheaf_map_map_apply]
    rfl
  have hm₂ := pullbackSection_map f (inf_le_right : U₁ ⊓ U₂ ≤ U₂) e₂
  have hm₁ := pullbackSection_map f (inf_le_left : U₁ ⊓ U₂ ≤ U₁) e₁
  rw [r U₂ h₂ inf_le_right, r U₁ h₁ inf_le_left, ← hm₂, ← hm₁, h, pullbackSection_smul,
    map_smul]

end AlgebraicGeometry.Scheme.Modules
