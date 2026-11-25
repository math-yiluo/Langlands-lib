/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementTensorCoordinates
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.StalkTensor

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits Opposite
open AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- Extension of a stalkwise pairing to the Godement tensor map.
Source: Banerjee, arXiv:1004.1491, §1.1.4, pp. 15–16; Stacks, Tag 0FKR.
(blueprint: new-module-cup-godement-tensor-map-of-pairing-exists)
The maps to each skyscraper coordinate are obtained from tensor universality and
sheafification, then assembled by the product universal property. -/
theorem moduleCup_godement_tensor_map_of_pairing_exists (X : Scheme.{u})
    (t : ∀ (H K : X.Modules) (x : X),
      H.presheaf.stalk x → K.presheaf.stalk x → (H ⊗ K).presheaf.stalk x)
    (ht : ∀ (H K : X.Modules) (x : X) (U : X.Opens) (hx : x ∈ U)
        (s : Γ(H, U)) (r : Γ(K, U)),
      t H K x (H.presheaf.germ U x hx s) (K.presheaf.germ U x hx r) =
        (H ⊗ K).presheaf.germ U x hx
          ((moduleCup_sectionTensor X H K).app (op U)
            (s ⊗ₜ[Γ(X, U)] r))) :
    ∃ b : ∀ H K : X.Modules,
      moduleCup_godementObject X H ⊗ moduleCup_godementObject X K ⟶
        moduleCup_godementObject X (H ⊗ K),
      ∀ (H K : X.Modules) (x : X) (U : X.Opens) (hx : x ∈ U)
        (s : Γ(moduleCup_godementObject X H, U))
        (r : Γ(moduleCup_godementObject X K, U)),
      (moduleCup_sectionTensor X (moduleCup_godementObject X H)
          (moduleCup_godementObject X K) ≫ (b H K).val ≫
        (Pi.π (fun y : X ↦ skyscraper y ((H ⊗ K).presheaf.stalk y)) x).val).app
          (op U) (s ⊗ₜ[Γ(X, U)] r) ⟨hx⟩ =
        t H K x
          ((Pi.π (fun y : X ↦ skyscraper y (H.presheaf.stalk y)) x).app U s ⟨hx⟩)
          ((Pi.π (fun y : X ↦ skyscraper y (K.presheaf.stalk y)) x).app U r ⟨hx⟩) := by
  classical
  -- The canonical stalk tensor comparison includes the sheafification step.
  have he (x : X) := SheafOfModules.stalkTensorIso X.toRingedSpace x
  choose e heG heNat using he
  have htensor (H K : X.Modules) (x : X) (U : X.Opens) (hx : x ∈ U)
      (s : Γ(H, U)) (r : Γ(K, U)) :
      (e x H K).hom ((H ⊗ K).presheaf.germ U x hx
        ((moduleCup_sectionTensor X H K).app (op U) (s ⊗ₜ[Γ(X, U)] r))) =
      H.presheaf.germ U x hx s ⊗ₜ[X.presheaf.stalk x] K.presheaf.germ U x hx r := by
    exact heG x H K U hx s r
  -- Represent both stalk elements on the intersection of their neighbourhoods.
  have hpair (H K : X.Modules) (x : X)
      (a : H.presheaf.stalk x) (b : K.presheaf.stalk x) :
      (e x H K).inv (a ⊗ₜ[X.presheaf.stalk x] b) = t H K x a b := by
    obtain ⟨U, hxU, s, rfl⟩ := H.presheaf.exists_germ_eq a
    obtain ⟨V, hxV, r, rfl⟩ := K.presheaf.exists_germ_eq b
    have hx : x ∈ U ⊓ V := ⟨hxU, hxV⟩
    rw [← H.presheaf.germ_res_apply (homOfLE inf_le_left : U ⊓ V ⟶ U) x hx s,
      ← K.presheaf.germ_res_apply (homOfLE inf_le_right : U ⊓ V ⟶ V) x hx r,
      ht H K x (U ⊓ V) hx,
      ← htensor H K x (U ⊓ V) hx]
    exact CategoryTheory.Iso.hom_inv_id_apply (e x H K) _
  let ev (H : X.Modules) (x : X) :
      (moduleCup_godementObject X H).presheaf.stalk x →ₗ[X.presheaf.stalk x]
        H.presheaf.stalk x :=
    skyscraperStalkEval x (H.presheaf.stalk x) ∘ₗ
      (Pi.π (fun y : X ↦ skyscraper y (H.presheaf.stalk y)) x).stalkLinearMap x
  have hev (H : X.Modules) (x : X) (U : X.Opens) (hx : x ∈ U)
      (s : Γ(moduleCup_godementObject X H, U)) :
      ev H x ((moduleCup_godementObject X H).presheaf.germ U x hx s) =
        (Pi.π (fun y : X ↦ skyscraper y (H.presheaf.stalk y)) x).app U s ⟨hx⟩ := by
    change skyscraperStalkEval x (H.presheaf.stalk x)
      ((Pi.π (fun y : X ↦ skyscraper y (H.presheaf.stalk y)) x).stalkLinearMap x
        ((moduleCup_godementObject X H).presheaf.germ U x hx s)) = _
    erw [Hom.stalkLinearMap_germ, skyscraperStalkEval_germ]
  -- Each coordinate is obtained from a linear map out of the tensor stalk.
  let l (H K : X.Modules) (x : X) :
      (moduleCup_godementObject X H ⊗ moduleCup_godementObject X K).presheaf.stalk x
        →ₗ[X.presheaf.stalk x] (H ⊗ K).presheaf.stalk x :=
    (e x H K).inv.hom ∘ₗ TensorProduct.map (ev H x) (ev K x) ∘ₗ
      (e x (moduleCup_godementObject X H) (moduleCup_godementObject X K)).hom.hom
  let b (H K : X.Modules) := Pi.lift fun x : X ↦ toSkyscraper (l H K x)
  refine ⟨b, ?_⟩
  intro H K x U hx s r
  have hcoord : b H K ≫
      Pi.π (fun y : X ↦ skyscraper y ((H ⊗ K).presheaf.stalk y)) x =
      toSkyscraper (l H K x) := Pi.lift_comp_π _ _
  have hv := congrArg (fun f ↦ f.val) hcoord
  rw [SheafOfModules.comp_val] at hv
  erw [hv]
  change (toSkyscraper (l H K x)).app U
    ((moduleCup_sectionTensor X (moduleCup_godementObject X H)
      (moduleCup_godementObject X K)).app (op U) (s ⊗ₜ[Γ(X, U)] r)) ⟨hx⟩ = _
  rw [toSkyscraper_app_apply]
  dsimp only [l, LinearMap.comp_apply]
  erw [htensor, TensorProduct.map_tmul, hpair]
  erw [hev, hev]

end
end AlgebraicGeometry.Scheme.Modules
