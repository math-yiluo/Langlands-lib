/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionCore
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionCore
import WeilConjectures.AlgebraicGeometry.ConstantScalarTensorModel

/-! # The ordinary reduction tower as a tensor tower

Source: Stacks Project, Modules on Sites, Tag 03EK and Tag 099M.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace CategoryTheory.ConstantCompletion
variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
variable (A : Type u) [CommRing A] (I : Ideal A)
attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

open ScalarTensorComparison

private theorem reductionTensorIso_step (b : Bool) (M : Mod (coefficients J A I b))
    (n : ℕ) :
    M ◁ (reductionStep J A I b n).app (𝟙_ _) ≫
        (reductionTensorIso J (finiteMap J A I b n) M).hom =
      (reductionTensorIso J (finiteMap J A I b (n + 1)) M).hom ≫
        (reductionStep J A I b n).app M := by
  apply reductionTensor_hom_ext J (finiteMap J A I b (n + 1)) M
  intro V s m
  change (reductionTensorIso J (finiteMap J A I b n) M).hom.val.app V
      ((M ◁ _).val.app V _) =
    ((reductionStep J A I b n).app M).val.app V
      ((reductionTensorIso J (finiteMap J A I b (n + 1)) M).hom.val.app V _)
  dsimp only [reduction, Functor.comp_obj] at *
  rw [← id_tensorHom, SheafOfModules.RingedTensor.pure_map]
  simp only [SheafOfModules.id_val, PresheafOfModules.id_app, ModuleCat.id_apply]
  erw [show ((reductionStep J A I b n).app (𝟙_ _)).val.app V
      (tensorSection (finiteMap J A I b (n + 1)) (𝟙_ _) V s
        (1 : (coefficients J A I b).obj.obj V)) = _ from
        (reductionStep_existsUnique J A I b n).exists.choose_spec (𝟙_ _) V s
          (1 : (coefficients J A I b).obj.obj V)]
  rw [reductionTensorIso_pure, reductionTensorIso_pure]
  exact ((reductionStep_existsUnique J A I b n).exists.choose_spec M V s m).symm

@[irreducible] private def reductionTensorNat (b : Bool)
    (M : Mod (coefficients J A I b)) :
    ((reductionTower J A I b).obj (𝟙_ _) ⋙
      (curriedTensor (Mod (coefficients J A I b))).flip).flip.obj M ⟶
        (reductionTower J A I b).obj M :=
  NatTrans.ofOpSequence (fun n ↦ (reductionTensorIso J (finiteMap J A I b n) M).hom)
    (fun n ↦ by
      change M ◁ ((reductionTower J A I b).obj (𝟙_ _)).map
          (homOfLE (Nat.le_succ n)).op ≫ _ =
        _ ≫ ((reductionTower J A I b).obj M).map (homOfLE (Nat.le_succ n)).op
      dsimp only [reductionTower, Functor.flip_obj_map]
      rw [Functor.ofOpSequence_map_homOfLE_succ]
      exact reductionTensorIso_step J A I b M n)

private theorem reductionTensorNat_app (b : Bool)
    (M : Mod (coefficients J A I b)) (n : ℕ) :
    (reductionTensorNat J A I b M).app (op n) =
      (reductionTensorIso J (finiteMap J A I b n) M).hom := by
  unfold reductionTensorNat
  rfl

private instance reductionTensorNat_isIso (b : Bool)
    (M : Mod (coefficients J A I b)) : IsIso (reductionTensorNat J A I b M) := by
  have : ∀ n, IsIso ((reductionTensorNat J A I b M).app n) := fun n ↦ by
    obtain ⟨n⟩ := n
    rw [reductionTensorNat_app]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

@[irreducible] private def reductionTensorTowerIso (b : Bool) :
    (((reductionTower J A I b).obj (𝟙_ _) ⋙
      (curriedTensor (Mod (coefficients J A I b))).flip).flip) ≅
        reductionTower J A I b :=
  NatIso.ofComponents (fun M ↦ asIso (reductionTensorNat J A I b M)) (by
    intro M N f
    apply NatTrans.ext
    funext n
    obtain ⟨n⟩ := n
    change f ▷ _ ≫ (reductionTensorNat J A I b N).app (op n) =
      (reductionTensorNat J A I b M).app (op n) ≫ _
    rw [reductionTensorNat_app, reductionTensorNat_app]
    exact reductionTensorIso_naturality J (finiteMap J A I b n) f)

private theorem reductionTensorTowerIso_hom_app (b : Bool)
    (M : Mod (coefficients J A I b)) (n : ℕ) :
    ((reductionTensorTowerIso J A I b).hom.app M).app (op n) =
      (reductionTensorIso J (finiteMap J A I b n) M).hom := by
  unfold reductionTensorTowerIso
  exact reductionTensorNat_app J A I b M n

/-- Restricted finite scalar extension is tensor with the reduction of the rank-one
module, naturally in the module and in the finite quotient level. This statement
involves ordinary module sheaves only, with no Koszul or cochain complex.

Source: Stacks Project, Modules on Sites, Tag 03EK; proetale.tex, Tag 099M.
(auxiliary; not a blueprint node).

Proof: identify restriction of scalar extension of M with the sheafification of
S tensor_R M. The reduction Q of the rank-one module is identified with the
restricted S-module S by multiplication. The symmetry of sheaf tensor identifies
M tensor_R Q with Q tensor_R M, and the normalized extension-tensor comparison
sends the pure tensor m tensor s to s tensor m. This constructs the component
isomorphisms. Pure tensors generate before sheafification, and the sheafification
adjunction detects maps from that sheafification. Thus the component maps commute
with every map of M and with the quotient transition s tensor m to bar(s) tensor m.
The reduction unit sends m to 1 tensor m; the displayed tensor unit map sends it
to m tensor 1. The same calculation proves the unit equation. All these formulas
hold for the empty site, zero ring, and zero or unit ideal. -/
theorem constantReductionTensorModel (b : Bool) :
    let O := coefficients J A I b
    let Q := (reductionTower J A I b).obj (𝟙_ (Mod O))
    ∃ e : reductionTower J A I b ≅ (Q ⋙ (curriedTensor (Mod O)).flip).flip,
      ∀ (M : Mod O) (n : ℕᵒᵖ),
        ((reductionUnit J A I b).app M).app n ≫ (e.hom.app M).app n =
          (ρ_ M).inv ≫ M ◁ ((reductionUnit J A I b).app (𝟙_ (Mod O))).app n := by
  let d := reductionTensorTowerIso J A I b
  refine ⟨d.symm, ?_⟩
  intro M n
  obtain ⟨n⟩ := n
  apply (cancel_mono ((d.hom.app M).app (op n))).1
  have hd : (d.inv.app M).app (op n) ≫ (d.hom.app M).app (op n) = 𝟙 _ :=
    congrArg (fun f ↦ f.app (op n)) (d.inv_hom_id_app M)
  simp only [Iso.symm_hom, Category.assoc, hd, Category.comp_id]
  rw [show ((d.hom.app M).app (op n)) =
    (reductionTensorIso J (finiteMap J A I b n) M).hom from
      reductionTensorTowerIso_hom_app J A I b M n]
  change ((reductionUnit J A I b).app M).app (op n) =
    (ρ_ M).inv ≫ M ◁ ((reductionUnit J A I b).app (𝟙_ _)).app (op n) ≫
      (reductionTensorIso J (finiteMap J A I b n) M).hom
  ext V m
  erw [(reductionUnit_existsUnique J A I b).exists.choose_spec]
  change _ = (reductionTensorIso J (finiteMap J A I b n) M).hom.val.app V
    ((M ◁ ((reductionUnit J A I b).app (𝟙_ _)).app (op n)).val.app V
      ((ρ_ M).inv.val.app V m))
  dsimp only [reductionTower, Functor.flip_obj_obj,
    reduction, Functor.comp_obj]
  erw [rightUnitor_inv_pure, ← id_tensorHom, SheafOfModules.RingedTensor.pure_map]
  simp only [SheafOfModules.id_val, PresheafOfModules.id_app, ModuleCat.id_apply]
  erw [(reductionUnit_existsUnique J A I b).exists.choose_spec]
  exact (reductionTensorIso_pure J (finiteMap J A I b n) M V 1 m).symm

end CategoryTheory.ConstantCompletion
