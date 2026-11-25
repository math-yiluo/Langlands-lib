/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementCodegeneracies
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import WeilConjectures.AlgebraicGeometry.ModuleCupGodementTensorCoordinatesExists
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

private lemma sectionTensor_natural (X : Scheme.{u}) {H K H' K' : X.Modules}
    (f : H ⟶ H') (g : K ⟶ K') :
    (f.val ⊗ₘ g.val) ≫ moduleCup_sectionTensor X H' K' =
      moduleCup_sectionTensor X H K ≫ (tensorHom (C := X.Modules) f g).val := by
  let S := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  have h : (tensorHom (C := X.Modules) f g) ≫
      (SheafOfModules.tensorObjIsoSheafification (R := X.sheaf) H' K').hom =
      (SheafOfModules.tensorObjIsoSheafification (R := X.sheaf) H K).hom ≫
        S.map (f.val ⊗ₘ g.val) := by
    rw [tensorHom_def, Category.assoc,
      SheafOfModules.whiskerLeft_tensorObjIsoSheafification_hom
        (R := X.sheaf) H' g,
      ← Category.assoc, SheafOfModules.whiskerRight_tensorObjIsoSheafification_hom
        (R := X.sheaf) f K,
      Category.assoc,
      ← Functor.map_comp]
    rw [← tensorHom_def]
  have hi : (SheafOfModules.tensorObjIsoSheafification (R := X.sheaf) H K).inv ≫
      (tensorHom (C := X.Modules) f g) = S.map (f.val ⊗ₘ g.val) ≫
        (SheafOfModules.tensorObjIsoSheafification (R := X.sheaf) H' K').inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← h]
    simp
  unfold moduleCup_sectionTensor
  have hu := (PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).unit.naturality (f.val ⊗ₘ g.val)
  dsimp at hu
  rw [← Category.assoc, hu, Category.assoc]
  have hiv := congrArg SheafOfModules.Hom.val hi.symm
  exact congrArg (fun z ↦ (PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).unit.app (H.val ⊗ K.val) ≫ z) hiv

private lemma tensor_hom_ext (X : Scheme.{u}) (H K L : X.Modules)
    (f g : H ⊗ K ⟶ L)
    (h : moduleCup_sectionTensor X H K ≫ f.val =
      moduleCup_sectionTensor X H K ≫ g.val) : f = g := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  have he : (SheafOfModules.tensorObjIsoSheafification (R := X.sheaf) H K).inv ≫ f =
      (SheafOfModules.tensorObjIsoSheafification (R := X.sheaf) H K).inv ≫ g := by
    apply (adj.homEquiv _ L).injective
    change adj.unit.app _ ≫ ((SheafOfModules.tensorObjIsoSheafification
      (R := X.sheaf) H K).inv ≫ f).val = adj.unit.app _ ≫
        ((SheafOfModules.tensorObjIsoSheafification (R := X.sheaf) H K).inv ≫ g).val
    simpa only [SheafOfModules.comp_val, Category.assoc, moduleCup_sectionTensor] using h
  exact (cancel_epi _).1 he

private lemma exists_common_germs (X : Scheme.{u}) (H K : X.Modules) (x : X)
    (a : H.presheaf.stalk x) (c : K.presheaf.stalk x) :
    ∃ (U : X.Opens) (hx : x ∈ U) (s : Γ(H, U)) (r : Γ(K, U)),
      H.presheaf.germ U x hx s = a ∧ K.presheaf.germ U x hx r = c := by
  obtain ⟨U, hu, s, rfl⟩ := H.presheaf.exists_germ_eq a
  obtain ⟨V, hv, r, rfl⟩ := K.presheaf.exists_germ_eq c
  refine ⟨U ⊓ V, ⟨hu, hv⟩, H.val.map (homOfLE inf_le_left).op s,
    K.val.map (homOfLE inf_le_right).op r, ?_, ?_⟩
  · exact H.presheaf.germ_res_apply _ x _ s
  · exact K.presheaf.germ_res_apply _ x _ r

private def proj (X : Scheme.{u}) (H : X.Modules) (x : X) :
    moduleCup_godementObject X H ⟶ skyscraper x (H.presheaf.stalk x) :=
  CategoryTheory.Limits.Pi.π (fun y : X ↦ skyscraper y (H.presheaf.stalk y)) x

private def eval (X : Scheme.{u}) (H : X.Modules) (x : X) :
    (moduleCup_godementObject X H).presheaf.stalk x →ₗ[X.presheaf.stalk x]
      H.presheaf.stalk x :=
  skyscraperStalkEval x (H.presheaf.stalk x) ∘ₗ (proj X H x).stalkLinearMap x

private lemma eval_germ (X : Scheme.{u}) (H : X.Modules) (x : X)
    (U : X.Opens) (hx : x ∈ U) (s : Γ(moduleCup_godementObject X H, U)) :
    eval X H x ((moduleCup_godementObject X H).presheaf.germ U x hx s) =
      (proj X H x).app U s ⟨hx⟩ := by
  simp only [eval, LinearMap.comp_apply, Hom.stalkLinearMap_germ, skyscraperStalkEval_germ]

private lemma tensor_germs_natural (X : Scheme.{u})
    (t : ∀ (H K : X.Modules) (x : X),
      H.presheaf.stalk x → K.presheaf.stalk x → (H ⊗ K).presheaf.stalk x)
    (ht : ∀ (H K : X.Modules) (x : X) (U : X.Opens) (hx : x ∈ U)
      (s : Γ(H, U)) (r : Γ(K, U)),
      t H K x (H.presheaf.germ U x hx s) (K.presheaf.germ U x hx r) =
        (H ⊗ K).presheaf.germ U x hx
          ((moduleCup_sectionTensor X H K).app (Opposite.op U) (s ⊗ₜ[Γ(X, U)] r)))
    {H K H' K' : X.Modules} (f : H ⟶ H') (g : K ⟶ K') (x : X)
    (a : H.presheaf.stalk x) (c : K.presheaf.stalk x) :
    t H' K' x (f.stalkLinearMap x a) (g.stalkLinearMap x c) =
      (f ⊗ₘ g).stalkLinearMap x (t H K x a c) := by
  obtain ⟨U, hx, s, r, rfl, rfl⟩ := exists_common_germs X H K x a c
  rw [Hom.stalkLinearMap_germ, Hom.stalkLinearMap_germ, ht, ht,
    Hom.stalkLinearMap_germ]
  apply congrArg ((H' ⊗ K').presheaf.germ U x hx)
  have hn := congrArg (fun z : H.val ⊗ K.val ⟶ (H' ⊗ K').val ↦
    z.app (Opposite.op U) (s ⊗ₜ[Γ(X, U)] r)) (sectionTensor_natural X f g)
  exact hn

private lemma map_eval_sections (X : Scheme.{u}) {H H' : X.Modules} (f : H ⟶ H')
    (x : X) (U : X.Opens) (hx : x ∈ U) (s : Γ(moduleCup_godementObject X H, U)) :
    (proj X H' x).app U ((moduleCup_godementMap X f).app U s) ⟨hx⟩ =
      f.stalkLinearMap x ((proj X H x).app U s ⟨hx⟩) := by
  have hp : moduleCup_godementMap X f ≫ proj X H' x =
      toSkyscraper (f.stalkLinearMap x ∘ₗ eval X H x) := by
    simp only [moduleCup_godementMap, proj, CategoryTheory.Limits.Pi.lift_comp_π, comp_toSkyscraper,
      eval, LinearMap.comp_assoc]
  change ((moduleCup_godementMap X f ≫ proj X H' x).app U s) ⟨hx⟩ = _
  rw [hp, toSkyscraper_app_apply, LinearMap.comp_apply, eval_germ]

private lemma coordinates_natural (X : Scheme.{u})
    (b : ∀ H K : X.Modules,
      moduleCup_godementObject X H ⊗ moduleCup_godementObject X K ⟶
        moduleCup_godementObject X (H ⊗ K))
    (hc : ModuleCupGodementTensorCoordinates X b)
    (H K H' K' : X.Modules) (f : H ⟶ H') (g : K ⟶ K') :
    (moduleCup_godementMap X f ⊗ₘ moduleCup_godementMap X g) ≫ b H' K' =
      b H K ≫ moduleCup_godementMap X (f ⊗ₘ g) := by
  obtain ⟨t, ht, hb⟩ := hc
  apply CategoryTheory.Limits.Pi.hom_ext
  intro x
  apply tensor_hom_ext X (moduleCup_godementObject X H) (moduleCup_godementObject X K)
  rw [SheafOfModules.comp_val, ← Category.assoc, SheafOfModules.comp_val,
    ← Category.assoc, ← sectionTensor_natural]
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro s r
  apply SkyscraperSections.ext
  intro hx
  have hb' := hb H' K' x V.unop hx
    ((moduleCup_godementMap X f).app V.unop s)
    ((moduleCup_godementMap X g).app V.unop r)
  change (proj X (H' ⊗ K') x).app V.unop
    ((b H' K').app V.unop
      ((moduleCup_sectionTensor X (moduleCup_godementObject X H')
        (moduleCup_godementObject X K')).app V
          (((moduleCup_godementMap X f).app V.unop s) ⊗ₜ[Γ(X, V.unop)]
            ((moduleCup_godementMap X g).app V.unop r)))) ⟨hx⟩ =
    (proj X (H' ⊗ K') x).app V.unop
      ((moduleCup_godementMap X (f ⊗ₘ g)).app V.unop
        ((b H K).app V.unop
          ((moduleCup_sectionTensor X (moduleCup_godementObject X H)
            (moduleCup_godementObject X K)).app V (s ⊗ₜ[Γ(X, V.unop)] r)))) ⟨hx⟩
  change (proj X (H' ⊗ K') x).app V.unop
    ((b H' K').app V.unop
      ((moduleCup_sectionTensor X (moduleCup_godementObject X H')
        (moduleCup_godementObject X K')).app V
          (((moduleCup_godementMap X f).app V.unop s) ⊗ₜ[Γ(X, V.unop)]
            ((moduleCup_godementMap X g).app V.unop r)))) ⟨hx⟩ = _ at hb'
  rw [hb', map_eval_sections]
  have hb0 := hb H K x V.unop hx s r
  change (proj X (H ⊗ K) x).app V.unop
    ((b H K).app V.unop
      ((moduleCup_sectionTensor X (moduleCup_godementObject X H)
        (moduleCup_godementObject X K)).app V (s ⊗ₜ[Γ(X, V.unop)] r))) ⟨hx⟩ = _ at hb0
  rw [hb0]
  change t H' K' x
    ((proj X H' x).app V.unop ((moduleCup_godementMap X f).app V.unop s) ⟨hx⟩)
    ((proj X K' x).app V.unop ((moduleCup_godementMap X g).app V.unop r) ⟨hx⟩) = _
  rw [map_eval_sections, map_eval_sections]
  exact tensor_germs_natural X t ht f g x _ _

private lemma coordinates_unit (X : Scheme.{u})
    (b : ∀ H K : X.Modules,
      moduleCup_godementObject X H ⊗ moduleCup_godementObject X K ⟶
        moduleCup_godementObject X (H ⊗ K))
    (hc : ModuleCupGodementTensorCoordinates X b) (H K : X.Modules) :
    (moduleCup_godementUnit X H ⊗ₘ moduleCup_godementUnit X K) ≫ b H K =
      moduleCup_godementUnit X (H ⊗ K) := by
  obtain ⟨t, ht, hb⟩ := hc
  apply CategoryTheory.Limits.Pi.hom_ext
  intro x
  apply tensor_hom_ext X H K
  rw [SheafOfModules.comp_val, ← Category.assoc, SheafOfModules.comp_val,
    ← Category.assoc, ← sectionTensor_natural]
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro s r
  apply SkyscraperSections.ext
  intro hx
  have hb' := hb H K x V.unop hx
    ((moduleCup_godementUnit X H).app V.unop s)
    ((moduleCup_godementUnit X K).app V.unop r)
  have hproj (L : X.Modules) :
      moduleCup_godementUnit X L ≫
        CategoryTheory.Limits.Pi.π (fun y : X ↦ skyscraper y (L.presheaf.stalk y)) x =
      toSkyscraper (LinearMap.id : L.presheaf.stalk x →ₗ[X.presheaf.stalk x]
        L.presheaf.stalk x) := by
    simp only [moduleCup_godementUnit, CategoryTheory.Limits.Pi.lift_comp_π]
  have heval (L : X.Modules) (a : Γ(L, V.unop)) :
      (CategoryTheory.Limits.Pi.π (fun y : X ↦ skyscraper y (L.presheaf.stalk y)) x).app V.unop
        ((moduleCup_godementUnit X L).app V.unop a) ⟨hx⟩ =
      L.presheaf.germ V.unop x hx a := by
    change ((moduleCup_godementUnit X L ≫
      CategoryTheory.Limits.Pi.π (fun y : X ↦ skyscraper y (L.presheaf.stalk y)) x).app
        V.unop a) ⟨hx⟩ = _
    rw [hproj]
    exact toSkyscraper_app_apply _ a hx
  simp only [heval] at hb'
  change (moduleCup_sectionTensor X (moduleCup_godementObject X H)
      (moduleCup_godementObject X K) ≫ (b H K).val ≫
      (CategoryTheory.Limits.Pi.π
        (fun y : X ↦ skyscraper y ((H ⊗ K).presheaf.stalk y)) x).val).app V
      (((moduleCup_godementUnit X H).app V.unop s) ⊗ₜ[Γ(X, V.unop)]
        ((moduleCup_godementUnit X K).app V.unop r)) ⟨hx⟩ = _
  rw [hb']
  rw [hproj]
  exact ht H K x V.unop hx s r

private lemma multiply_eval_sections (X : Scheme.{u}) (H : X.Modules)
    (x : X) (U : X.Opens) (hx : x ∈ U)
    (s : Γ(moduleCup_godementObject X (moduleCup_godementObject X H), U)) :
    (proj X H x).app U ((moduleCup_godementMultiply X H).app U s) ⟨hx⟩ =
      eval X H x ((proj X (moduleCup_godementObject X H) x).app U s ⟨hx⟩) := by
  have hp : moduleCup_godementMultiply X H ≫ proj X H x =
      toSkyscraper (eval X H x ∘ₗ eval X (moduleCup_godementObject X H) x) := by
    simp only [moduleCup_godementMultiply, proj, CategoryTheory.Limits.Pi.lift_comp_π,
      comp_toSkyscraper, eval, LinearMap.comp_assoc]
  change ((moduleCup_godementMultiply X H ≫ proj X H x).app U s) ⟨hx⟩ = _
  rw [hp, toSkyscraper_app_apply, LinearMap.comp_apply, eval_germ]

private lemma coordinates_multiply (X : Scheme.{u})
    (b : ∀ H K : X.Modules,
      moduleCup_godementObject X H ⊗ moduleCup_godementObject X K ⟶
        moduleCup_godementObject X (H ⊗ K))
    (hc : ModuleCupGodementTensorCoordinates X b) (H K : X.Modules) :
    (moduleCup_godementMultiply X H ⊗ₘ moduleCup_godementMultiply X K) ≫ b H K =
      b (moduleCup_godementObject X H) (moduleCup_godementObject X K) ≫
        moduleCup_godementMap X (b H K) ≫ moduleCup_godementMultiply X (H ⊗ K) := by
  obtain ⟨t, ht, hb⟩ := hc
  have he (x : X) (a : (moduleCup_godementObject X H).presheaf.stalk x)
      (c : (moduleCup_godementObject X K).presheaf.stalk x) :
      eval X (H ⊗ K) x ((b H K).stalkLinearMap x
        (t (moduleCup_godementObject X H) (moduleCup_godementObject X K) x a c)) =
      t H K x (eval X H x a) (eval X K x c) := by
    obtain ⟨U, hx, s, r, rfl, rfl⟩ := exists_common_germs X
      (moduleCup_godementObject X H) (moduleCup_godementObject X K) x a c
    rw [ht, Hom.stalkLinearMap_germ, eval_germ, eval_germ, eval_germ]
    exact hb H K x U hx s r
  apply CategoryTheory.Limits.Pi.hom_ext
  intro x
  apply tensor_hom_ext X (moduleCup_godementObject X (moduleCup_godementObject X H))
    (moduleCup_godementObject X (moduleCup_godementObject X K))
  rw [SheafOfModules.comp_val, ← Category.assoc, SheafOfModules.comp_val,
    ← Category.assoc, ← sectionTensor_natural]
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro s r
  apply SkyscraperSections.ext
  intro hx
  change (proj X (H ⊗ K) x).app V.unop
    ((b H K).app V.unop
      ((moduleCup_sectionTensor X (moduleCup_godementObject X H)
        (moduleCup_godementObject X K)).app V
          (((moduleCup_godementMultiply X H).app V.unop s) ⊗ₜ[Γ(X, V.unop)]
            ((moduleCup_godementMultiply X K).app V.unop r)))) ⟨hx⟩ =
    (proj X (H ⊗ K) x).app V.unop
      ((moduleCup_godementMultiply X (H ⊗ K)).app V.unop
        ((moduleCup_godementMap X (b H K)).app V.unop
          ((b (moduleCup_godementObject X H) (moduleCup_godementObject X K)).app
            V.unop ((moduleCup_sectionTensor X
              (moduleCup_godementObject X (moduleCup_godementObject X H))
              (moduleCup_godementObject X (moduleCup_godementObject X K))).app
                V (s ⊗ₜ[Γ(X, V.unop)] r))))) ⟨hx⟩
  have hb1 := hb H K x V.unop hx
    ((moduleCup_godementMultiply X H).app V.unop s)
    ((moduleCup_godementMultiply X K).app V.unop r)
  have hb2 := hb (moduleCup_godementObject X H) (moduleCup_godementObject X K)
    x V.unop hx s r
  change (proj X (H ⊗ K) x).app V.unop
    ((b H K).app V.unop
      ((moduleCup_sectionTensor X (moduleCup_godementObject X H)
        (moduleCup_godementObject X K)).app V
          (((moduleCup_godementMultiply X H).app V.unop s) ⊗ₜ[Γ(X, V.unop)]
            ((moduleCup_godementMultiply X K).app V.unop r)))) ⟨hx⟩ = _ at hb1
  rw [hb1, multiply_eval_sections, map_eval_sections]
  change t H K x
    ((proj X H x).app V.unop ((moduleCup_godementMultiply X H).app V.unop s) ⟨hx⟩)
    ((proj X K x).app V.unop ((moduleCup_godementMultiply X K).app V.unop r) ⟨hx⟩) = _
  rw [multiply_eval_sections, multiply_eval_sections]
  change (proj X (moduleCup_godementObject X H ⊗ moduleCup_godementObject X K) x).app
    V.unop ((b (moduleCup_godementObject X H) (moduleCup_godementObject X K)).app
      V.unop ((moduleCup_sectionTensor X
        (moduleCup_godementObject X (moduleCup_godementObject X H))
        (moduleCup_godementObject X (moduleCup_godementObject X K))).app
          V (s ⊗ₜ[Γ(X, V.unop)] r))) ⟨hx⟩ = _ at hb2
  rw [hb2]
  exact (he x _ _).symm


/-- The coordinatewise Godement tensor maps obey naturality, unit and multiplication laws.
Source: Banerjee, arXiv:1004.1491, §1.1.4, pp. 15–16; Stacks, Tag 0FKR.
(blueprint: new-module-cup-godement-beta-exists)
Proof: For each point x, project TH and TK onto their x skyscrapers and evaluate their
stalks at x. Identify (TH tensor TK)_x with TH_x tensor TK_x by the canonical
stalk tensor isomorphism. Tensor the two evaluation maps into H_x tensor K_x, then
use the stalk tensor isomorphism into (H tensor K)_x. The skyscraper adjunction gives
a morphism from TH tensor TK to the
skyscraper of (H tensor K)_x; product universality assembles these into b. Naturality
is checked after each product projection on tensors of local representatives, where
both composites apply the two stalk maps to the same representatives. For the unit
law these representatives are germs of sections of H and K, and both composites give
the germ of their tensor. For multiplication, choose a common neighbourhood for the
outer germs and inner representatives: both composites evaluate the inner x
coordinates and tensor them. Equality on pure tensors, the stalk colimit universal
property, the skyscraper adjunction and product extensionality prove the laws.
The argument also applies to empty products and zero module sheaves. -/
theorem moduleCup_godement_beta_maps_exists (X : Scheme.{u}) :
    ∃ b : ∀ H K : X.Modules,
        moduleCup_godementObject X H ⊗ moduleCup_godementObject X K ⟶
          moduleCup_godementObject X (H ⊗ K),
      (∀ (H K H' K' : X.Modules) (f : H ⟶ H') (g : K ⟶ K'),
        (moduleCup_godementMap X f ⊗ₘ moduleCup_godementMap X g) ≫ b H' K' =
          b H K ≫ moduleCup_godementMap X (f ⊗ₘ g)) ∧
      (∀ H K : X.Modules,
        (moduleCup_godementUnit X H ⊗ₘ moduleCup_godementUnit X K) ≫ b H K =
          moduleCup_godementUnit X (H ⊗ K)) ∧
      (∀ H K : X.Modules,
        (moduleCup_godementMultiply X H ⊗ₘ moduleCup_godementMultiply X K) ≫ b H K =
          b (moduleCup_godementObject X H) (moduleCup_godementObject X K) ≫
            moduleCup_godementMap X (b H K) ≫ moduleCup_godementMultiply X (H ⊗ K)) := by
  obtain ⟨b, hc⟩ := moduleCup_godement_tensor_coordinates_exists X
  exact ⟨b, coordinates_natural X b hc, coordinates_unit X b hc,
    coordinates_multiply X b hc⟩

end
end AlgebraicGeometry.Scheme.Modules
