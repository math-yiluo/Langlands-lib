/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementTensorCoordinates

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits Opposite
open AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

private lemma tensor_restrict (X : Scheme.{u}) (H K : X.Modules)
    {U V : X.Opens} (i : V ⟶ U) (s : Γ(H, U)) (r : Γ(K, U)) :
    (H ⊗ K).presheaf.map i.op
        ((moduleCup_sectionTensor X H K).app (op U) (s ⊗ₜ[Γ(X, U)] r)) =
      (moduleCup_sectionTensor X H K).app (op V)
        (H.presheaf.map i.op s ⊗ₜ[Γ(X, V)] K.presheaf.map i.op r) := by
  exact (PresheafOfModules.naturality_apply (moduleCup_sectionTensor X H K)
    i.op (s ⊗ₜ[Γ(X, U)] r)).symm

private lemma tensor_germ_restrict (X : Scheme.{u}) (H K : X.Modules) (x : X)
    {U V : X.Opens} (hxU : x ∈ U) (hxV : x ∈ V) (i : V ⟶ U)
    (s : Γ(H, U)) (r : Γ(K, U)) :
    (H ⊗ K).presheaf.germ V x hxV
        ((moduleCup_sectionTensor X H K).app (op V)
          (H.presheaf.map i.op s ⊗ₜ[Γ(X, V)] K.presheaf.map i.op r)) =
      (H ⊗ K).presheaf.germ U x hxU
        ((moduleCup_sectionTensor X H K).app (op U) (s ⊗ₜ[Γ(X, U)] r)) := by
  rw [← tensor_restrict X H K i s r]
  exact (H ⊗ K).presheaf.germ_res_apply i x hxV _

private lemma tensor_germ_eq (X : Scheme.{u}) (H K : X.Modules) (x : X)
    {U V : X.Opens} (hxU : x ∈ U) (hxV : x ∈ V)
    (s : Γ(H, U)) (r : Γ(K, U)) (s' : Γ(H, V)) (r' : Γ(K, V))
    (hs : H.presheaf.germ U x hxU s = H.presheaf.germ V x hxV s')
    (hr : K.presheaf.germ U x hxU r = K.presheaf.germ V x hxV r') :
    (H ⊗ K).presheaf.germ U x hxU
        ((moduleCup_sectionTensor X H K).app (op U) (s ⊗ₜ[Γ(X, U)] r)) =
      (H ⊗ K).presheaf.germ V x hxV
        ((moduleCup_sectionTensor X H K).app (op V) (s' ⊗ₜ[Γ(X, V)] r')) := by
  obtain ⟨W, hxW, iU, iV, hs⟩ := H.presheaf.germ_eq x hxU hxV s s' hs
  obtain ⟨Z, hxZ, jU, jV, hr⟩ := K.presheaf.germ_eq x hxU hxV r r' hr
  -- Refine the two neighbourhoods on which the input representatives agree.
  let kW : W ⊓ Z ⟶ W := homOfLE inf_le_left
  let kZ : W ⊓ Z ⟶ Z := homOfLE inf_le_right
  have hs' := congrArg (H.presheaf.map kW.op) hs
  have hr' := congrArg (K.presheaf.map kZ.op) hr
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp] at hs' hr'
  rw [← tensor_germ_restrict X H K x (V := W ⊓ Z) hxU ⟨hxW, hxZ⟩ (kW ≫ iU),
    ← tensor_germ_restrict X H K x (V := W ⊓ Z) hxV ⟨hxW, hxZ⟩ (kW ≫ iV)]
  apply congrArg ((H ⊗ K).presheaf.germ (W ⊓ Z) x ⟨hxW, hxZ⟩)
  apply congrArg ((moduleCup_sectionTensor X H K).app (op (W ⊓ Z)))
  apply congrArg₂ (fun a b ↦ a ⊗ₜ[Γ(X, W ⊓ Z)] b)
  · simpa only [op_comp] using hs'
  · have eU : (kW ≫ iU).op = jU.op ≫ kZ.op := Subsingleton.elim _ _
    have eV : (kW ≫ iV).op = jV.op ≫ kZ.op := Subsingleton.elim _ _
    rw [eU, eV]
    exact hr'

private lemma exists_common_germs (X : Scheme.{u}) (H K : X.Modules) (x : X)
    (a : H.presheaf.stalk x) (b : K.presheaf.stalk x) :
    ∃ (U : X.Opens) (hx : x ∈ U) (s : Γ(H, U)) (r : Γ(K, U)),
      H.presheaf.germ U x hx s = a ∧ K.presheaf.germ U x hx r = b := by
  obtain ⟨U, hu, s, rfl⟩ := H.presheaf.exists_germ_eq a
  obtain ⟨V, hv, r, rfl⟩ := K.presheaf.exists_germ_eq b
  refine ⟨U ⊓ V, ⟨hu, hv⟩, H.val.map (homOfLE inf_le_left).op s,
    K.val.map (homOfLE inf_le_right).op r, ?_, ?_⟩
  · exact H.presheaf.germ_res_apply _ x _ s
  · exact K.presheaf.germ_res_apply _ x _ r

/-- Existence of the stalkwise pairing used in the coordinate construction.
Source: Banerjee, arXiv:1004.1491, §1.1.4, pp. 15–16.
(blueprint: new-module-cup-godement-tensor-stalk-pairing-exists)
The pairing sends germs represented on a common neighbourhood to the germ of the
sectionwise tensor. Compatibility under restriction makes this well-defined, and
bilinearity follows from bilinearity of the presheaf tensor product. -/
theorem moduleCup_godement_tensor_stalk_pairing_exists (X : Scheme.{u}) :
    ∃ t : ∀ (H K : X.Modules) (x : X),
      H.presheaf.stalk x → K.presheaf.stalk x → (H ⊗ K).presheaf.stalk x,
    ∀ (H K : X.Modules) (x : X) (U : X.Opens) (hx : x ∈ U)
        (s : Γ(H, U)) (r : Γ(K, U)),
      t H K x (H.presheaf.germ U x hx s) (K.presheaf.germ U x hx r) =
        (H ⊗ K).presheaf.germ U x hx
          ((moduleCup_sectionTensor X H K).app (op U)
            (s ⊗ₜ[Γ(X, U)] r)) := by
  classical
  -- Choose actual section representatives; their tensor germ is independent of the choice.
  choose U hx s r hs hr using exists_common_germs X
  refine ⟨fun H K x a b ↦ (H ⊗ K).presheaf.germ (U H K x a b) x (hx H K x a b)
    ((moduleCup_sectionTensor X H K).app (op (U H K x a b))
      (s H K x a b ⊗ₜ[Γ(X, U H K x a b)] r H K x a b)), ?_⟩
  intro H K x V hxV v w
  exact tensor_germ_eq X H K x _ hxV _ _ v w (hs H K x _ _) (hr H K x _ _)

end
end AlgebraicGeometry.Scheme.Modules
