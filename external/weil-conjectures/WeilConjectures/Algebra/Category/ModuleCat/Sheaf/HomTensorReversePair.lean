/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomTensorPair

/-! # Reverse currying for one pair of module sheaves

Source: Stacks Project, Modules on Sites, Tag 03EO; Cohomology on Sites, Tag 0A90.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits Opposite

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max u v})

set_option hygiene false in
set_option quotPrecheck false in
local notation "Mod" => SheafOfModules.{max u v}
  ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)

set_option synthInstance.maxSize 256 in
set_option backward.isDefEq.respectTransparency false in
/-- Curry a map from one tensor product, keeping the source parameter sheaf.
Source: Stacks Project, Modules on Sites, Lemma internal-hom-adjoint-tensor (03EO).
(blueprint: lem-sc-hom-tensor-reverse-pair).

Proof: For a section s over U, precompose its localized tensor map with the
presheaf-to-sheaf tensor map. For x over W/U, define the local map on B over W
by sending y over V/W to the original map on V applied to x restricted to V
tensor y. Its linearity follows from balanced bilinearity. Naturality follows
from naturality of the original tensor map and the tensor sheafification unit.
The construction is linear in x and s and commutes with restriction in U,
so it gives a morphism into the two internal Homs. Evaluation at the identity
object over W restricts x by the identity and hence gives the stated equation.
Zero modules and zero input sections are covered by the same linear formulas;
no global pure-tensor generation is used. -/
theorem homTensorReversePair_construct (S A B D : Mod) :
    letI := monoidalCategory R
    ∀ f : S ⟶ homObj (R := R) (A ⊗ B) D,
    ∃ b : S ⟶ homObj (R := R) A (homObj (R := R) B D),
      ∀ (U : Cᵒᵖ) (s : S.val.obj U) (W : (Over U.unop)ᵒᵖ)
        (x : A.val.obj (op W.unop.left)) (y : B.val.obj (op W.unop.left)),
        (((f.val.app U).hom s).app W).hom
          (((CategoryTheory.homTensorCurrySectionMap R A B).app
            (op W.unop.left)).hom (x ⊗ₜ[R.obj.obj (op W.unop.left)] y)) =
        (((((b.val.app U).hom s).app W).hom x).app
          (op (Over.mk (𝟙 W.unop.left)))).hom y  := by
  classical
  let := monoidalCategory R
  intro f
  let τ := CategoryTheory.homTensorCurrySectionMap R A B
  let f' := PresheafOfModules.tensorHomUncurry_pair f.val
  let φ : B.val ⊗ (A.val ⊗ S.val) ⟶ D.val :=
    (α_ B.val A.val S.val).inv ≫ ((β_ B.val A.val).hom ▷ S.val) ≫
      (τ ▷ S.val) ≫ f'
  let b : S ⟶ homObj (R := R) A (homObj (R := R) B D) :=
    ⟨PresheafOfModules.tensorHomCurry_pair
      (PresheafOfModules.tensorHomCurry_pair φ)⟩
  refine ⟨b, ?_⟩
  intro U s W x y
  let V := op W.unop.left
  change _ = (φ.app V).hom
    (y ⊗ₜ[R.obj.obj V] (A.val ⊗ S.val).map (𝟙 W.unop.left).op
      (x ⊗ₜ[R.obj.obj V] S.val.map W.unop.hom.op s))
  rw [op_id, PresheafOfModules.map_id]
  change _ = ((((f.val.app V).hom (S.val.map W.unop.hom.op s)).app
    (op (Over.mk (𝟙 W.unop.left)))).hom ((τ.app V).hom (x ⊗ₜ[R.obj.obj V] y)))
  have hf := PresheafOfModules.naturality_apply f.val W.unop.hom.op s
  change (f.val.app V).hom (S.val.map W.unop.hom.op s) =
    PresheafOfModules.restrictOverMap W.unop.hom ((f.val.app U).hom s) at hf
  rw [hf]
  exact (PresheafOfModules.restrictOver_hom_app_congr ((f.val.app U).hom s)
    (Category.id_comp W.unop.hom) ((τ.app V).hom (x ⊗ₜ[R.obj.obj V] y))).symm

end SheafOfModules
