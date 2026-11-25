/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.PullbackMonoidal
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit

@[expose] public section
set_option autoImplicit false
set_option linter.style.longLine false
universe u
open CategoryTheory MonoidalCategory Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance] presheafMonoidalCategory sheafificationMonoidal
  forgetToPresheafOfModulesLaxMonoidal

private lemma sheafification_δ_unit_tmul {X : Scheme.{u}}
    (P Q : _root_.PresheafOfModules.{u} X.ringCatSheaf.obj)
    (U : X.Opens) (s : P.obj (op U)) (t : Q.obj (op U)) :
    (Functor.OplaxMonoidal.δ (sheafification X) P Q).app U
      (((sheafificationAdjunction X).unit.app (P ⊗ Q)).app (op U) (s ⊗ₜ t)) =
    tmulSection (((sheafificationAdjunction X).unit.app P).app (op U) s)
      (((sheafificationAdjunction X).unit.app Q).app (op U) t) := by
  have h := (sheafificationAdjunction X).unit_app_tensor_comp_map_δ P Q
  have hh := congrArg (fun φ ↦ φ.app (op U) (s ⊗ₜ t)) h
  simp only [_root_.PresheafOfModules.comp_app, ConcreteCategory.comp_apply] at hh
  erw [_root_.PresheafOfModules.tensorHom_app_tmul] at hh
  exact hh

private lemma pullback_sheafification_unit {X Y : Scheme.{u}} (f : Y ⟶ X)
    (P : _root_.PresheafOfModules.{u} X.ringCatSheaf.obj) (U : X.Opens) (s : P.obj (op U)) :
    Hom.app (X := Y)
      ((SheafOfModules.sheafificationCompPullback f.toRingCatSheafHom).hom.app P) (f ⁻¹ᵁ U)
      (pullbackUnitApp f ((sheafification X).obj P) U
        (((sheafificationAdjunction X).unit.app P).app (op U) s)) =
    ((sheafificationAdjunction Y).unit.app
      ((_root_.PresheafOfModules.pullbackOfCommRingCat f.toRingCatPresheafHom).obj P)).app
      (op (f ⁻¹ᵁ U))
      (((_root_.PresheafOfModules.adjunctionOfCommRingCat f.toRingCatPresheafHom).unit.app P).app
        (op U) s) := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    ((sheafificationAdjunction X).comp (pullbackPushforwardAdjunction f))
    ((_root_.PresheafOfModules.adjunctionOfCommRingCat f.toRingCatPresheafHom).comp
      (sheafificationAdjunction Y)) P
  rw [Adjunction.comp_unit_app, Adjunction.comp_unit_app] at h
  have hh := congrArg (fun φ ↦ φ.app (op U) s) h
  simp only [_root_.PresheafOfModules.comp_app, ConcreteCategory.comp_apply] at hh
  exact hh

private lemma pullback_sheafification_δ {X Y : Scheme.{u}} (f : Y ⟶ X)
    (P Q : _root_.PresheafOfModules.{u} X.ringCatSheaf.obj) :
    (pullback f).map (Functor.OplaxMonoidal.δ (sheafification X) P Q) ≫
      Functor.OplaxMonoidal.δ (pullback f) _ _ ≫
      ((SheafOfModules.sheafificationCompPullback f.toRingCatSheafHom).hom.app P ⊗ₘ
        (SheafOfModules.sheafificationCompPullback f.toRingCatSheafHom).hom.app Q) =
    (SheafOfModules.sheafificationCompPullback f.toRingCatSheafHom).hom.app (P ⊗ Q) ≫
      (sheafification Y).map (Functor.OplaxMonoidal.δ
        (_root_.PresheafOfModules.pullbackOfCommRingCat f.toRingCatPresheafHom) P Q) ≫
      Functor.OplaxMonoidal.δ (sheafification Y) _ _ := by
  let := presheafPullbackCompSheafificationMonoidal f
  let e : sheafification X ⋙ pullback f ≅
      _root_.PresheafOfModules.pullbackOfCommRingCat f.toRingCatPresheafHom ⋙ sheafification Y :=
    SheafOfModules.sheafificationCompPullback f.toRingCatSheafHom
  have he : e.hom.IsMonoidal := by
    exact Localization.Monoidal.lifting_isMonoidal (sheafification X)
      ((Opens.grothendieckTopology X).W.inverseImage
        (_root_.PresheafOfModules.toPresheaf X.ringCatSheaf.obj)) (pullback f)
      (_root_.PresheafOfModules.pullbackOfCommRingCat f.toRingCatPresheafHom ⋙ sheafification Y)
  let := he
  change Functor.OplaxMonoidal.δ (sheafification X ⋙ pullback f) P Q ≫
    (e.hom.app P ⊗ₘ e.hom.app Q) = e.hom.app (P ⊗ Q) ≫
      Functor.OplaxMonoidal.δ
        (_root_.PresheafOfModules.pullbackOfCommRingCat f.toRingCatPresheafHom ⋙ sheafification Y)
        P Q
  rw [← cancel_epi (Functor.LaxMonoidal.μ (sheafification X ⋙ pullback f) P Q)]
  simp only [← Category.assoc, Functor.Monoidal.μ_δ, Category.id_comp]
  rw [NatTrans.IsMonoidal.tensor (τ := e.hom), Category.assoc,
    Functor.Monoidal.μ_δ, Category.comp_id]

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private lemma presheafPullback_δ_unit_tmul
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {F : C ⥤ D} {R : Dᵒᵖ ⥤ CommRingCat.{u}} {S : Cᵒᵖ ⥤ CommRingCat.{u}}
    (φ : S ⋙ forget₂ CommRingCat RingCat ⟶ (F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat)
    (P Q : _root_.PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat))
    (U : C) (s : P.obj (op U)) (t : Q.obj (op U)) :
    (Functor.OplaxMonoidal.δ (_root_.PresheafOfModules.pullbackOfCommRingCat φ) P Q).app
      (op (F.obj U))
      (((_root_.PresheafOfModules.adjunctionOfCommRingCat φ).unit.app (P ⊗ Q)).app
        (op U) (s ⊗ₜ t)) =
    (show ((_root_.PresheafOfModules.pullbackOfCommRingCat φ).obj P).obj (op (F.obj U)) from
      ((_root_.PresheafOfModules.adjunctionOfCommRingCat φ).unit.app P).app (op U) s) ⊗ₜ
    (show ((_root_.PresheafOfModules.pullbackOfCommRingCat φ).obj Q).obj (op (F.obj U)) from
      ((_root_.PresheafOfModules.adjunctionOfCommRingCat φ).unit.app Q).app (op U) t) := by
  have h := _root_.PresheafOfModules.adjunctionOfCommRingCat_homEquiv_δ φ P Q
  rw [Adjunction.homEquiv_unit] at h
  have hh := congrArg (fun k ↦ k.app (op U) (s ⊗ₜ t)) h
  simp only [_root_.PresheafOfModules.comp_app] at hh
  have ht := _root_.PresheafOfModules.tensorHom_app_tmul (R := S)
    ((_root_.PresheafOfModules.adjunctionOfCommRingCat φ).unit.app P)
    ((_root_.PresheafOfModules.adjunctionOfCommRingCat φ).unit.app Q) (op U) s t
  refine hh.trans ((congrArg (fun z ↦
    (Functor.LaxMonoidal.μ (_root_.PresheafOfModules.pushforwardOfCommRingCat φ)
      ((_root_.PresheafOfModules.pullbackOfCommRingCat φ).obj P)
      ((_root_.PresheafOfModules.pullbackOfCommRingCat φ).obj Q)).app (op U) z) ht).trans ?_)
  exact _root_.PresheafOfModules.pushforward_μ_app_tmul φ
    ((_root_.PresheafOfModules.pullbackOfCommRingCat φ).obj P)
    ((_root_.PresheafOfModules.pullbackOfCommRingCat φ).obj Q) (op U) _ _

set_option backward.isDefEq.respectTransparency false in
private lemma pullback_δ_sheafification_sections {X Y : Scheme.{u}} (f : Y ⟶ X)
    (P Q : _root_.PresheafOfModules.{u} X.ringCatSheaf.obj)
    (U : X.Opens) (s : P.obj (op U)) (t : Q.obj (op U)) :
    (Functor.OplaxMonoidal.δ (pullback f)
      ((sheafification X).obj P) ((sheafification X).obj Q)).app (f ⁻¹ᵁ U)
      (pullbackUnitApp f ((sheafification X).obj P ⊗ (sheafification X).obj Q) U
        (tmulSection (((sheafificationAdjunction X).unit.app P).app (op U) s)
          (((sheafificationAdjunction X).unit.app Q).app (op U) t))) =
    tmulSection
      (pullbackUnitApp f ((sheafification X).obj P) U
        (((sheafificationAdjunction X).unit.app P).app (op U) s))
      (pullbackUnitApp f ((sheafification X).obj Q) U
        (((sheafificationAdjunction X).unit.app Q).app (op U) t)) := by
  let e : sheafification X ⋙ pullback f ≅
      _root_.PresheafOfModules.pullbackOfCommRingCat f.toRingCatPresheafHom ⋙ sheafification Y :=
    SheafOfModules.sheafificationCompPullback f.toRingCatSheafHom
  apply (ConcreteCategory.bijective_of_isIso ((e.hom.app P ⊗ₘ e.hom.app Q).app
    (f ⁻¹ᵁ U))).1
  rw [tensorHom_app_tmulSection]
  dsimp only [e]
  erw [pullback_sheafification_unit f P U s, pullback_sheafification_unit f Q U t]
  have h := congrArg (fun φ ↦ φ.app (f ⁻¹ᵁ U)
    (pullbackUnitApp f ((sheafification X).obj (P ⊗ Q)) U
      (((sheafificationAdjunction X).unit.app (P ⊗ Q)).app (op U) (s ⊗ₜ t))))
    (pullback_sheafification_δ f P Q)
  change _ = (Functor.OplaxMonoidal.δ (sheafification Y) _ _).app (f ⁻¹ᵁ U)
    (((sheafification Y).map (Functor.OplaxMonoidal.δ
      (_root_.PresheafOfModules.pullbackOfCommRingCat f.toRingCatPresheafHom) P Q)).app
      (f ⁻¹ᵁ U)
      (Hom.app (X := Y)
        ((SheafOfModules.sheafificationCompPullback f.toRingCatSheafHom).hom.app (P ⊗ Q))
        (f ⁻¹ᵁ U)
        (pullbackUnitApp f ((sheafification X).obj (P ⊗ Q)) U
          (((sheafificationAdjunction X).unit.app (P ⊗ Q)).app (op U) (s ⊗ₜ t))))) at h
  simp only [Hom.comp_app, ConcreteCategory.comp_apply] at h
  erw [pullbackUnit_naturality_apply f
    (Functor.OplaxMonoidal.δ (sheafification X) P Q) U,
    sheafification_δ_unit_tmul P Q U s t,
    pullback_sheafification_unit f (P ⊗ Q) U (s ⊗ₜ t)] at h
  change _ = (Functor.OplaxMonoidal.δ (sheafification Y) _ _).app (f ⁻¹ᵁ U)
    (((sheafification Y).map (Functor.OplaxMonoidal.δ
      (_root_.PresheafOfModules.pullbackOfCommRingCat f.toRingCatPresheafHom) P Q)).app
      (f ⁻¹ᵁ U) _) at h
  have hn := (sheafificationAdjunction Y).unit.naturality
    (Functor.OplaxMonoidal.δ
      (_root_.PresheafOfModules.pullbackOfCommRingCat f.toRingCatPresheafHom) P Q)
  have hs := congrArg (fun φ ↦ φ.app (op (f ⁻¹ᵁ U))
    (((_root_.PresheafOfModules.adjunctionOfCommRingCat f.toRingCatPresheafHom).unit.app
      (P ⊗ Q)).app (op U) (s ⊗ₜ t))) hn
  simp only [_root_.PresheafOfModules.comp_app, ConcreteCategory.comp_apply] at hs
  erw [← hs, presheafPullback_δ_unit_tmul f.toRingCatPresheafHom P Q U s t] at h
  exact h.trans (sheafification_δ_unit_tmul
    ((_root_.PresheafOfModules.pullbackOfCommRingCat f.toRingCatPresheafHom).obj P)
    ((_root_.PresheafOfModules.pullbackOfCommRingCat f.toRingCatPresheafHom).obj Q) (f ⁻¹ᵁ U)
    (show ((_root_.PresheafOfModules.pullbackOfCommRingCat f.toRingCatPresheafHom).obj P).obj
      (op (f ⁻¹ᵁ U)) from
      ((_root_.PresheafOfModules.adjunctionOfCommRingCat f.toRingCatPresheafHom).unit.app P).app
        (op U) s)
    (show ((_root_.PresheafOfModules.pullbackOfCommRingCat f.toRingCatPresheafHom).obj Q).obj
      (op (f ⁻¹ᵁ U)) from
      ((_root_.PresheafOfModules.adjunctionOfCommRingCat f.toRingCatPresheafHom).unit.app Q).app
        (op U) t))


set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types false in
private lemma pullback_tensor_unit_map {X Y : Scheme.{u}} (f : Y ⟶ X)
    {A B M N : X.Modules} (φ : A ⟶ M) (ψ : B ⟶ N) (U : X.Opens)
    (s : Γ(A, U)) (t : Γ(B, U))
    (h : (Functor.OplaxMonoidal.δ (pullback f) A B).app (f ⁻¹ᵁ U)
      (pullbackUnitApp f (A ⊗ B) U (tmulSection s t)) =
      tmulSection (pullbackUnitApp f A U s) (pullbackUnitApp f B U t)) :
    (Functor.OplaxMonoidal.δ (pullback f) M N).app (f ⁻¹ᵁ U)
      (pullbackUnitApp f (M ⊗ N) U (tmulSection (φ.app U s) (ψ.app U t))) =
      tmulSection (pullbackUnitApp f M U (φ.app U s))
        (pullbackUnitApp f N U (ψ.app U t)) := by
  have hn :
      (Functor.OplaxMonoidal.δ (pullback f) M N).app (f ⁻¹ᵁ U)
        (((pullback f).map (φ ⊗ₘ ψ)).app (f ⁻¹ᵁ U)
          (pullbackUnitApp f (A ⊗ B) U (tmulSection s t))) =
      ((pullback f).map φ ⊗ₘ (pullback f).map ψ).app (f ⁻¹ᵁ U)
        ((Functor.OplaxMonoidal.δ (pullback f) A B).app (f ⁻¹ᵁ U)
          (pullbackUnitApp f (A ⊗ B) U (tmulSection s t))) := by
    exact congrArg (fun k ↦ k.app (f ⁻¹ᵁ U)
      (pullbackUnitApp f (A ⊗ B) U (tmulSection s t)))
      (Functor.OplaxMonoidal.δ_natural (pullback f) φ ψ).symm
  calc
    _ = (Functor.OplaxMonoidal.δ (pullback f) M N).app (f ⁻¹ᵁ U)
        (((pullback f).map (φ ⊗ₘ ψ)).app (f ⁻¹ᵁ U)
          (pullbackUnitApp f (A ⊗ B) U (tmulSection s t))) := by
      apply congrArg
      exact ((pullbackUnit_naturality_apply f (φ ⊗ₘ ψ) U (tmulSection s t)).trans
        (congrArg (pullbackUnitApp f (M ⊗ N) U)
          (tensorHom_app_tmulSection φ ψ s t))).symm
    _ = _ := hn
    _ = ((pullback f).map φ ⊗ₘ (pullback f).map ψ).app (f ⁻¹ᵁ U)
        (tmulSection (pullbackUnitApp f A U s) (pullbackUnitApp f B U t)) :=
      congrArg _ h
    _ = _ := (tensorHom_app_tmulSection ((pullback f).map φ) ((pullback f).map ψ)
      (pullbackUnitApp f A U s) (pullbackUnitApp f B U t)).trans
      (congrArg₂ tmulSection (pullbackUnit_naturality_apply f φ U s)
        (pullbackUnit_naturality_apply f ψ U t))



/-- A single pullback cotensorator sends the adjunction unit on an elementary
section tensor to the tensor of the two unit sections.
Source: Stacks Project, Tag 0095, Definition 6.26.1(2); Tag 0096.
(blueprint: lem-sc-pullback-tensor-unit-section)

Proof: On presheaves the pullback cotensorator is the adjoint of the pushforward
lax tensorator. The adjunction unit inserts coefficient 1; the pushforward
tensorator sends a pure tensor to the same pure tensor after restriction of
scalars. Thus its adjoint sends 1 tensor (s tensor t) to
(1 tensor s) tensor (1 tensor t). Sheafification carries elementary presheaf
tensors to tmulSection. The comparison sheafificationCompPullback is defined
by uniqueness of left adjoints, so it carries the presheaf adjunction unit to
the sheaf adjunction unit. The monoidal localization defining pullbackMonoidal
transports exactly this presheaf cotensorator. Applying the transported formula
therefore gives the displayed equality. This concerns only one morphism and
two sections; it requires neither composition coherence nor a unit-object
coherence assertion. Zero sections, zero rings, empty opens and identity
morphisms all obey the same coefficient-1 formula. -/
theorem pullback_δ_app_unit_tmulSection
    {X Y : Scheme.{u}} (f : Y ⟶ X) (M N : X.Modules) (U : X.Opens)
    (s : Γ(M, U)) (t : Γ(N, U)) :
    (Functor.OplaxMonoidal.δ (pullback f) M N).app (f ⁻¹ᵁ U)
        (pullbackUnitApp f (M ⊗ N) U (tmulSection s t)) =
      tmulSection (pullbackUnitApp f M U s) (pullbackUnitApp f N U t) := by
  let P := (forgetToPresheafOfModules X).obj M
  let Q := (forgetToPresheafOfModules X).obj N
  let cM : (sheafification X).obj P ⟶ M := (sheafificationAdjunction X).counit.app M
  let cN : (sheafification X).obj Q ⟶ N := (sheafificationAdjunction X).counit.app N
  have hs : cM.app U (((sheafificationAdjunction X).unit.app P).app (op U) s) = s := by
    have h := (sheafificationAdjunction X).right_triangle_components M
    exact congrArg (fun φ ↦ φ.app (op U) s) h
  have ht : cN.app U (((sheafificationAdjunction X).unit.app Q).app (op U) t) = t := by
    have h := (sheafificationAdjunction X).right_triangle_components N
    exact congrArg (fun φ ↦ φ.app (op U) t) h
  have h := pullback_δ_sheafification_sections f P Q U s t
  have hh := pullback_tensor_unit_map f cM cN U
    (((sheafificationAdjunction X).unit.app P).app (op U) s)
    (((sheafificationAdjunction X).unit.app Q).app (op U) t) h
  simpa only [hs, ht] using hh

end AlgebraicGeometry.Scheme.Modules
