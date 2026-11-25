/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

import WeilConjectures.AlgebraicGeometry.ChangeOfRingsTensorActionMaps
import WeilConjectures.AlgebraicGeometry.ChangeOfRingsTensorBalancingUniversal

/-! # Change of rings as a tensor relation cokernel

Source: Stacks Project, Morphisms, proof of Lemma 01SB; Sheaves, Lemma 0089.
(blueprint: lem-weil-pbc-change-of-rings-tensor-relation-presentation).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme.Modules

set_option hygiene false in
local notation "𝓡" S => (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj S
set_option hygiene false in
local notation "𝓻" a => (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map a

/-- A universal equalizing morphism presents the cokernel of the difference. -/
private theorem exists_cokernelIso_of_equalizing_universal
    {D : Type*} [Category D] [Preadditive D] {R S T : D}
    (a d : R ⟶ S) (g : S ⟶ T) (hag : a ≫ g = d ≫ g)
    (hu : ∀ (Q : D) (f : S ⟶ Q), a ≫ f = d ≫ f → ∃! t : T ⟶ Q, g ≫ t = f)
    [HasCokernel (a - d)] :
    ∃ e : T ≅ cokernel (a - d), g ≫ e.hom = cokernel.π (a - d) := by
  let δ := a - d
  have hδg : δ ≫ g = 0 := by
    rw [Preadditive.sub_comp, hag, sub_self]
  let q := cokernel.π δ
  have hq : a ≫ q = d ≫ q := by
    apply sub_eq_zero.mp
    rw [← Preadditive.sub_comp]
    exact cokernel.condition δ
  obtain ⟨h, hh, _⟩ := hu (cokernel δ) q hq
  let k : cokernel δ ⟶ T := cokernel.desc δ g hδg
  have hqk : q ≫ k = g := cokernel.π_desc δ g hδg
  have hhk : h ≫ k = 𝟙 T := by
    obtain ⟨_, _, htuniq⟩ := hu T g hag
    apply (htuniq (h ≫ k) ?_).trans (htuniq (𝟙 T) ?_).symm
    · rw [← Category.assoc, hh, hqk]
    · exact Category.comp_id g
  have hkh : k ≫ h = 𝟙 (cokernel δ) := by
    apply (cancel_epi q).mp
    rw [← Category.assoc, hqk, hh, Category.comp_id]
  let e : T ≅ cokernel δ :=
    { hom := h
      inv := k
      hom_inv_id := hhk
      inv_hom_id := hkh }
  exact ⟨e, hh⟩

/-- The tensor relation presentation, without any quasi-coherence hypotheses.
Source: Stacks Project, Morphisms, proof of Lemma 01SB (change of rings), and
Sheaves, Lemma 0089 (sheafification universal property).
(blueprint: lem-weil-pbc-change-of-rings-tensor-relation-presentation).

Proof: on the tensor presheaf C tensor_O P, define the two B-actions by acting
on P and by multiplication through φ on C. They commute with restrictions and
extend uniquely to its sheafification S. Their difference induces δ from B tensor_O S.
The balanced tensor map from C tensor_O P to C tensor_B P kills δ and gives a map
from coker δ to change of rings. Conversely, the cokernel projection composed with
the tensor sheafification unit kills all B-balancing relations, hence factors through
C tensor_B P and then through its sheafification. Both composites are identities:
on S this follows from the sheafification universal property and cancellation of the
cokernel projection; on change of rings use surjectivity of the presheaf balancing
map followed by uniqueness of sheafification. These maps give e. Evaluating the
constructions on pure tensors gives the displayed relation and comparison formulas.
-/
theorem changeOfRings_tensor_relation_presentation (Y : Scheme.{u})
    (B C : Y.CommAlgebraSheaf) (φ : B ⟶ C)
    (P : SheafOfModules.{u} (𝓡 B.right)) :
    let P₀ := (SheafOfModules.restrictScalars (𝓻 B.hom)).obj P
    let S := tensorObj C.toModule P₀
    ∃ (δ : tensorObj B.toModule S ⟶ S)
      (e : (SheafOfModules.restrictScalars (𝓻 C.hom)).obj
        (SheafOfModules.changeOfRings.{u, u, u} φ.right P) ≅ cokernel δ),
      (∀ (W : Y.Opens) (b : B.right.obj.obj (op W))
          (c : C.right.obj.obj (op W)) (p : P.val.obj (op W)),
        δ.app W (tmulSection (M := B.toModule) b
          (tmulSection (M := C.toModule) (N := P₀) c p)) =
          tmulSection (M := C.toModule) (N := P₀) c (b • p) -
            tmulSection (M := C.toModule) (N := P₀) (φ.right.hom.app (op W) b * c) p) ∧
      (∀ (W : Y.Opens) (c : C.right.obj.obj (op W)) (p : P.val.obj (op W)),
        e.hom.val.app (op W)
          ((((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 C.right).obj)).unit.app
            (SheafOfModules.changeOfRingsPresheaf.{u, u, u} φ.right P)).app (op W))
              (c ⊗ₜ[B.right.obj.obj (op W), (φ.right.hom.app (op W)).hom] p)) =
          (cokernel.π δ).app W (tmulSection (M := C.toModule) (N := P₀) c p)) := by
  classical
  intro P₀ S
  refine (exists_changeOfRings_tensor_action_maps Y B C φ P).elim fun a ha ↦ ?_
  refine ha.elim fun d hd ↦ ?_
  refine hd.elim fun g hactions ↦ ?_
  have hu := changeOfRings_tensor_balancing_universal
    Y B C φ P a d g hactions.1 hactions.2.1 hactions.2.2.1
  have hag := hactions.2.2.2
  let δ : tensorObj B.toModule S ⟶ S := a - d
  refine (exists_cokernelIso_of_equalizing_universal a d g hag hu).elim fun e hh ↦ ?_
  refine ⟨δ, e, ?_, ?_⟩
  · intro W b c p
    exact congrArg₂ (· - ·) (hactions.1 W b c p) (hactions.2.1 W b c p)
  · intro W c p
    exact (congrArg (e.hom.val.app (op W)) (hactions.2.2.1 W c p).symm).trans
      (congrArg (fun f : S ⟶ cokernel δ ↦
        f.app W (tmulSection (M := C.toModule) (N := P₀) c p)) hh)

end AlgebraicGeometry.Scheme.Modules
