/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementCodegeneracies
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible

/-! # Coordinates of the Godement tensor pairing -/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits Opposite
open AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- The canonical map from sectionwise tensors to the sheaf tensor product.
Source: the sheafification adjunction; Banerjee, §1.1.4.
(blueprint: new-module-cup-godement-tensor-coordinates) -/
def moduleCup_sectionTensor (X : Scheme.{u}) (H K : X.Modules) :
    H.val ⊗ K.val ⟶ (H ⊗ K).val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
      (H.val ⊗ K.val) ≫
    (SheafOfModules.tensorObjIsoSheafification (R := X.sheaf) H K).inv.val

/-- The coordinate characterization fixes the tensor pairing without imposing its laws.
Here `t` is the tensor of stalk germs, characterized by sectionwise pure tensors; each
coordinate of `b` tensors the two evaluated Godement coordinates.
Source: Banerjee, §1.1.4, pp. 15–16; Stacks, Tag 0FKR.
(blueprint: new-module-cup-godement-tensor-coordinates) -/
def ModuleCupGodementTensorCoordinates (X : Scheme.{u})
    (b : ∀ H K : X.Modules,
      moduleCup_godementObject X H ⊗ moduleCup_godementObject X K ⟶
        moduleCup_godementObject X (H ⊗ K)) : Prop :=
  ∃ t : ∀ (H K : X.Modules) (x : X),
      H.presheaf.stalk x → K.presheaf.stalk x → (H ⊗ K).presheaf.stalk x,
    (∀ (H K : X.Modules) (x : X) (U : X.Opens) (hx : x ∈ U)
        (s : Γ(H, U)) (r : Γ(K, U)),
      t H K x (H.presheaf.germ U x hx s) (K.presheaf.germ U x hx r) =
        (H ⊗ K).presheaf.germ U x hx
          ((moduleCup_sectionTensor X H K).app (op U)
            (s ⊗ₜ[Γ(X, U)] r))) ∧
    (∀ (H K : X.Modules) (x : X) (U : X.Opens) (hx : x ∈ U)
        (s : Γ(moduleCup_godementObject X H, U))
        (r : Γ(moduleCup_godementObject X K, U)),
      (moduleCup_sectionTensor X (moduleCup_godementObject X H)
          (moduleCup_godementObject X K) ≫ (b H K).val ≫
        (Pi.π (fun y : X ↦ skyscraper y ((H ⊗ K).presheaf.stalk y)) x).val).app
          (op U) (s ⊗ₜ[Γ(X, U)] r) ⟨hx⟩ =
        t H K x
          ((Pi.π (fun y : X ↦ skyscraper y (H.presheaf.stalk y)) x).app U s ⟨hx⟩)
          ((Pi.π (fun y : X ↦ skyscraper y (K.presheaf.stalk y)) x).app U r ⟨hx⟩))

end
end AlgebraicGeometry.Scheme.Modules
