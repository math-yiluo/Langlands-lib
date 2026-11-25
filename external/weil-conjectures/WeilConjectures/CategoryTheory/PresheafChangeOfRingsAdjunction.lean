/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
public import Mathlib.Topology.Sheaves.Sheaf
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.MonoidalCompat

/-!
# Change of rings for presheaves of modules

Source: Stacks Project, Sheaves, Tag 006R (blueprint: lem-pc-presheaf-change-of-rings-adjunction)
-/

@[expose] public section


universe u v w

open CategoryTheory
open scoped ChangeOfRings

namespace PresheafOfModules

variable (X : TopCat.{u}) (A B : X.Sheaf CommRingCat.{w}) (α : A ⟶ B)

local notation "R" => (A.presheaf ⋙ forget₂ CommRingCat RingCat)
local notation "S" => (B.presheaf ⋙ forget₂ CommRingCat RingCat)
local notation "a" => Functor.whiskerRight α.hom (forget₂ CommRingCat RingCat)

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private noncomputable def tensorRestriction (M : PresheafOfModules.{max v w} R)
    {U V : (TopologicalSpace.Opens X)ᵒᵖ} (i : U ⟶ V) :
    (ModuleCat.extendScalars (α.hom.app U).hom).obj (M.obj U) ⟶
      (ModuleCat.restrictScalars (B.presheaf.map i).hom).obj
        ((ModuleCat.extendScalars (α.hom.app V).hom).obj (M.obj V)) := by
  let : Module (A.presheaf.obj V) (B.presheaf.obj V) :=
    Module.compHom (B.presheaf.obj V) (α.hom.app V).hom
  let T := (ModuleCat.restrictScalars (B.presheaf.map i).hom).obj
    ((ModuleCat.extendScalars (α.hom.app V).hom).obj (M.obj V))
  let h : M.obj U ⟶ (ModuleCat.restrictScalars (α.hom.app U).hom).obj T :=
    ModuleCat.ofHom (Y := (ModuleCat.restrictScalars (α.hom.app U).hom).obj T)
      { toFun := fun m ↦ (1 : B.presheaf.obj V) ⊗ₜ[A.presheaf.obj V,
          (α.hom.app V).hom] M.map i m
        map_add' := by
          intro m n
          rw [map_add, TensorProduct.tmul_add]
        map_smul' := by
          intro r m
          change (1 : B.presheaf.obj V) ⊗ₜ[A.presheaf.obj V, (α.hom.app V).hom]
            M.map i (r • m) = B.presheaf.map i (α.hom.app U r) •
              ((1 : B.presheaf.obj V) ⊗ₜ[A.presheaf.obj V, (α.hom.app V).hom] M.map i m)
          rw [M.map_smul]
          have hn : B.presheaf.map i (α.hom.app U r) =
              α.hom.app V (A.presheaf.map i r) :=
            ConcreteCategory.congr_hom (α.hom.naturality i).symm r
          rw [hn]
          change (1 : B.presheaf.obj V) ⊗ₜ[A.presheaf.obj V]
            ((A.presheaf.map i r) • (show M.obj V from M.map i m)) = _
          rw [TensorProduct.tmul_smul]
          rfl }
  exact ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
    («R» := A.presheaf.obj U) («S» := B.presheaf.obj U) (α.hom.app U).hom h

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem tensorRestriction_tmul (M : PresheafOfModules.{max v w} R)
    {U V : (TopologicalSpace.Opens X)ᵒᵖ} (i : U ⟶ V)
    (b : B.presheaf.obj U) (m : M.obj U) :
    tensorRestriction X A B α M i (b ⊗ₜ[A.presheaf.obj U, (α.hom.app U).hom] m) =
      B.presheaf.map i b ⊗ₜ[A.presheaf.obj V, (α.hom.app V).hom] M.map i m := by
  let : Module (A.presheaf.obj V) (B.presheaf.obj V) :=
    Module.compHom (B.presheaf.obj V) (α.hom.app V).hom
  let T := (ModuleCat.restrictScalars (B.presheaf.map i).hom).obj
    ((ModuleCat.extendScalars (α.hom.app V).hom).obj (M.obj V))
  let : Module (A.presheaf.obj U) T := Module.compHom T (α.hom.app U).hom
  let : Module (A.presheaf.obj U) (B.presheaf.obj U) :=
    Module.compHom (B.presheaf.obj U) (α.hom.app U).hom
  unfold tensorRestriction
  erw [ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_hom_apply,
    TensorProduct.lift.tmul]
  change B.presheaf.map i b •
    ((1 : B.presheaf.obj V) ⊗ₜ[A.presheaf.obj V, (α.hom.app V).hom] M.map i m) = _
  rw [ModuleCat.ExtendScalars.smul_tmul, mul_one]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private noncomputable def tensorPresheaf (M : PresheafOfModules.{max v w} R) :
    PresheafOfModules.{max v w} S where
  obj U := (ModuleCat.extendScalars (α.hom.app U).hom).obj (M.obj U)
  map i := tensorRestriction X A B α M i
  map_id U := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    rw [tensorRestriction_tmul]
    simp
    rfl
  map_comp {U V W} i j := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    simp only [ModuleCat.comp_apply, tensorRestriction_tmul]
    change _ = tensorRestriction X A B α M j _
    erw [tensorRestriction_tmul]
    simp
    rfl

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private noncomputable def tensorToRestrict
    (M : PresheafOfModules.{max v w} R) (N : PresheafOfModules.{max v w} S)
    (f : tensorPresheaf X A B α M ⟶ N) : M ⟶ (restrictScalars a).obj N where
  app U := ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.toRestrictScalars
    (α.hom.app U).hom (f.app U)
  naturality := by
    intro U V i
    ext m
    change f.app V ((1 : B.presheaf.obj V) ⊗ₜ[A.presheaf.obj V,
      (α.hom.app V).hom] M.map i m) =
      N.map i (f.app U ((1 : B.presheaf.obj U) ⊗ₜ[A.presheaf.obj U,
        (α.hom.app U).hom] m))
    rw [← naturality_apply f i]
    change _ = f.app V (tensorRestriction X A B α M i _)
    rw [tensorRestriction_tmul]
    simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private noncomputable def tensorFromRestrict
    (M : PresheafOfModules.{max v w} R) (N : PresheafOfModules.{max v w} S)
    (g : M ⟶ (restrictScalars a).obj N) : tensorPresheaf X A B α M ⟶ N where
  app U := ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
    («R» := A.presheaf.obj U) («S» := B.presheaf.obj U) (α.hom.app U).hom (g.app U)
  naturality := by
    intro U V i
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    change ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
      («R» := A.presheaf.obj V) («S» := B.presheaf.obj V) (α.hom.app V).hom (g.app V)
        (tensorRestriction X A B α M i _) =
      N.map i (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
        («R» := A.presheaf.obj U) («S» := B.presheaf.obj U) (α.hom.app U).hom (g.app U) _)
    rw [tensorRestriction_tmul]
    simp only [map_one]
    let : Module (A.presheaf.obj V) (B.presheaf.obj V) :=
      Module.compHom (B.presheaf.obj V) (α.hom.app V).hom
    let : Module (A.presheaf.obj V) (N.obj V) :=
      Module.compHom (N.obj V) (α.hom.app V).hom
    let : Module (A.presheaf.obj U) (B.presheaf.obj U) :=
      Module.compHom (B.presheaf.obj U) (α.hom.app U).hom
    let : Module (A.presheaf.obj U) (N.obj U) :=
      Module.compHom (N.obj U) (α.hom.app U).hom
    erw [ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_hom_apply
      («R» := A.presheaf.obj V) («S» := B.presheaf.obj V), TensorProduct.lift.tmul,
      ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_hom_apply
      («R» := A.presheaf.obj U) («S» := B.presheaf.obj U), TensorProduct.lift.tmul]
    change (1 : B.presheaf.obj V) • (show N.obj V from g.app V (M.map i m)) =
      N.map i ((1 : B.presheaf.obj U) • (show N.obj U from g.app U m))
    simp only [one_smul]
    exact naturality_apply g i m

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private noncomputable def tensorHomEquiv
    (M : PresheafOfModules.{max v w} R) (N : PresheafOfModules.{max v w} S) :
    (tensorPresheaf X A B α M ⟶ N) ≃ (M ⟶ (restrictScalars a).obj N) where
  toFun := tensorToRestrict X A B α M N
  invFun := tensorFromRestrict X A B α M N
  left_inv f := by
    apply hom_ext
    intro U
    exact (ModuleCat.ExtendRestrictScalarsAdj.homEquiv (α.hom.app U).hom).left_inv _
  right_inv g := by
    apply hom_ext
    intro U
    exact (ModuleCat.ExtendRestrictScalarsAdj.homEquiv (α.hom.app U).hom).right_inv _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem tensorHomEquiv_symm_tmul
    (M : PresheafOfModules.{max v w} R) (N : PresheafOfModules.{max v w} S)
    (g : M ⟶ (restrictScalars a).obj N) (U : (TopologicalSpace.Opens X)ᵒᵖ)
    (b : B.presheaf.obj U) (m : M.obj U) :
    ((tensorHomEquiv X A B α M N).symm g).app U
      (b ⊗ₜ[A.presheaf.obj U, (α.hom.app U).hom] m) =
        b • (show N.obj U from g.app U m) := by
  let : Module (A.presheaf.obj U) (B.presheaf.obj U) :=
    Module.compHom (B.presheaf.obj U) (α.hom.app U).hom
  let : Module (A.presheaf.obj U) (N.obj U) :=
    Module.compHom (N.obj U) (α.hom.app U).hom
  change ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
    («R» := A.presheaf.obj U) («S» := B.presheaf.obj U) (α.hom.app U).hom (g.app U) _ = _
  erw [ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_hom_apply
    («R» := A.presheaf.obj U) («S» := B.presheaf.obj U), TensorProduct.lift.tmul]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The sectionwise tensor presheaf is left adjoint to restriction of scalars.
The witnesses `T` and `q` present the tensor presheaf functor by sectionwise
`B(U)`-linear isomorphisms from `B(U) ⊗[A(U)] M(U)`. The first two clauses specify
its restrictions and its action on morphisms. The equivalences `e` have the
unit and inverse formulas and are natural in both module presheaves.

Source: Stacks Project, Sheaves, Tag 006R, lemma-adjointness-tensor-restrict-presheaves,
and the definitions immediately preceding it.
(blueprint: lem-pc-presheaf-change-of-rings-adjunction)

Proof (the four steps of the node):
1. Restrict scalars using `a`; the ring morphism's naturality gives semilinear
restrictions. Form sectionwise base change [def-weil-module-base-change]; the tensor
universal property [def-weil-pbc-module-tensor-product] defines restrictions by
`b ⊗ m ↦ b|V ⊗ m|V`. Identity, composition and semilinearity hold on pure tensors,
which generate. This is a presheaf of modules [def-weil-presheaf-modules-sheafification].
2. Apply the scalar-extension Hom equivalence [lem-weil-pbc-scalar-extension-hom]
to each section ring map: forward evaluation on `1 ⊗ m`, inverse `b ⊗ m ↦ b • w(m)`.
3. Forward restriction compatibility follows by evaluating on `1 ⊗ m` and `1|V = 1`.
Inverse compatibility follows on `b ⊗ m` from semilinearity of the restrictions of `N`
and compatibility of `w`; tensor generation extends it to every element
[def-weil-pbc-module-tensor-product]. The sectionwise inverses give inverse presheaf
morphisms [def-weil-presheaf-modules-sheafification], hence the equivalences `e`.
4. For `f : M ⟶ M'`, sectionwise `id ⊗ f` commutes with restrictions on pure tensors
and thus everywhere [def-weil-module-base-change, def-weil-pbc-module-tensor-product].
Evaluate on `1 ⊗ m` to get naturality in `M`. Postcomposition with `β : N ⟶ N'`
gives naturality in `N` by the sectionwise formula [lem-weil-pbc-scalar-extension-hom]. -/
theorem changeOfRingsAdjunction :
    ∃ (T : PresheafOfModules.{max v w} R ⥤ PresheafOfModules.{max v w} S)
      (q : ∀ (M : PresheafOfModules.{max v w} R) (U : (TopologicalSpace.Opens X)ᵒᵖ),
        (ModuleCat.extendScalars (α.hom.app U).hom).obj (M.obj U) ≅ (T.obj M).obj U)
      (e : ∀ (M : PresheafOfModules.{max v w} R) (N : PresheafOfModules.{max v w} S),
        (T.obj M ⟶ N) ≃ (M ⟶ (restrictScalars a).obj N)),
      (∀ (M : PresheafOfModules.{max v w} R)
        (U V : (TopologicalSpace.Opens X)ᵒᵖ) (i : U ⟶ V)
        (b : B.presheaf.obj U) (m : M.obj U),
        (T.obj M).map i ((q M U).hom (b ⊗ₜ[A.presheaf.obj U,(α.hom.app U).hom] m)) =
          (q M V).hom ((B.presheaf.map i b) ⊗ₜ[A.presheaf.obj V,(α.hom.app V).hom]
            (M.map i m))) ∧
      (∀ (M M' : PresheafOfModules.{max v w} R) (f : M ⟶ M')
        (U : (TopologicalSpace.Opens X)ᵒᵖ) (b : B.presheaf.obj U) (m : M.obj U),
        (T.map f).app U ((q M U).hom (b ⊗ₜ[A.presheaf.obj U,(α.hom.app U).hom] m)) =
          (q M' U).hom (b ⊗ₜ[A.presheaf.obj U,(α.hom.app U).hom] (f.app U m))) ∧
      (∀ (M : PresheafOfModules.{max v w} R) (N : PresheafOfModules.{max v w} S)
        (f : T.obj M ⟶ N) (U : (TopologicalSpace.Opens X)ᵒᵖ) (m : M.obj U),
        (e M N f).app U m =
          f.app U ((q M U).hom ((1 : B.presheaf.obj U) ⊗ₜ[A.presheaf.obj U,
            (α.hom.app U).hom] m))) ∧
      (∀ (M : PresheafOfModules.{max v w} R) (N : PresheafOfModules.{max v w} S)
        (g : M ⟶ (restrictScalars a).obj N) (U : (TopologicalSpace.Opens X)ᵒᵖ)
        (b : B.presheaf.obj U) (m : M.obj U),
        ((e M N).symm g).app U
            ((q M U).hom (b ⊗ₜ[A.presheaf.obj U,(α.hom.app U).hom] m)) =
          b • (show N.obj U from g.app U m)) ∧
      (∀ (M M' : PresheafOfModules.{max v w} R) (N : PresheafOfModules.{max v w} S)
        (f : M ⟶ M') (h : T.obj M' ⟶ N),
        e M N (T.map f ≫ h) = f ≫ e M' N h) ∧
      (∀ (M : PresheafOfModules.{max v w} R) (N N' : PresheafOfModules.{max v w} S)
        (β : N ⟶ N') (h : T.obj M ⟶ N),
        e M N' (h ≫ β) = e M N h ≫ (restrictScalars a).map β) := by
  let e := tensorHomEquiv X A B α
  have hn : ∀ M N N' (β : N ⟶ N') (h : tensorPresheaf X A B α M ⟶ N),
      e M N' (h ≫ β) = e M N h ≫ (restrictScalars a).map β := by
    intros
    rfl
  let T := Adjunction.leftAdjointOfEquiv e hn
  have ht (M M' : PresheafOfModules.{max v w} R) (f : M ⟶ M')
      (U : (TopologicalSpace.Opens X)ᵒᵖ) (b : B.presheaf.obj U) (m : M.obj U) :
      (T.map f).app U (b ⊗ₜ[A.presheaf.obj U, (α.hom.app U).hom] m) =
        b ⊗ₜ[A.presheaf.obj U, (α.hom.app U).hom] (f.app U m) := by
    change ((e M (tensorPresheaf X A B α M')).symm
      (f ≫ e M' (tensorPresheaf X A B α M') (𝟙 _))).app U _ = _
    rw [tensorHomEquiv_symm_tmul]
    change b • ((1 : B.presheaf.obj U) ⊗ₜ[A.presheaf.obj U,
      (α.hom.app U).hom] (f.app U m)) = _
    rw [ModuleCat.ExtendScalars.smul_tmul, mul_one]
  refine ⟨T, fun M U ↦ Iso.refl _, e, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro M U V i b m
    exact tensorRestriction_tmul X A B α M i b m
  · intro M M' f U b m
    exact ht M M' f U b m
  · intro M N f U m
    rfl
  · intro M N g U b m
    exact tensorHomEquiv_symm_tmul X A B α M N g U b m
  · intro M M' N f h
    ext U m
    change h.app U ((T.map f).app U
      ((1 : B.presheaf.obj U) ⊗ₜ[A.presheaf.obj U, (α.hom.app U).hom] m)) =
      h.app U ((1 : B.presheaf.obj U) ⊗ₜ[A.presheaf.obj U,
        (α.hom.app U).hom] (f.app U m))
    rw [ht]
  · exact hn

end PresheafOfModules
