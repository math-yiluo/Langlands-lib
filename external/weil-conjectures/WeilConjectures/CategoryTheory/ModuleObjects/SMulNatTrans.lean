/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal

/-!
# Multiplication by a global section on module objects

Let `C` be a braided monoidal category and `S : C` a commutative algebra object. A global section
`t : 𝟙 ⟶ S` acts on every `S`-module object `M` by `m ↦ t m`, that is by
`M ≅ 𝟙 ⊗ M ⟶ S ⊗ M ⟶ M`. Since `S` is commutative, this is `S`-linear, and it is natural in
`M`: this is the natural endomorphism `Mod.smulNatTrans t` of the identity functor of `Mod C S`.

When `C` has coequalizers preserved by tensoring, so that `Mod C S` is monoidal for the relative
tensor product, multiplication by `t` on `M ⊗_S N` is `M ⊗_S (t •)` (`Mod.smulNatTrans_app_tensor`).
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory BraidedCategory MonObj Limits

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {S : C} [MonObj S]

/-- The multiplication `M ⟶ M`, `m ↦ t m`, by a global section `t : 𝟙 ⟶ S` on an `S`-module
object `M`, as a morphism in `C`. -/
noncomputable abbrev smulHom (t : 𝟙_ C ⟶ S) (M : Mod C S) : M.X ⟶ M.X :=
  (λ_ M.X).inv ≫ t ▷ M.X ≫ γ[S,M.X]

/-- Multiplication by a global section commutes with `S`-linear maps. -/
@[reassoc]
lemma smulHom_naturality (t : 𝟙_ C ⟶ S) {M N : Mod C S} (f : M ⟶ N) :
    smulHom t M ≫ f.hom = f.hom ≫ smulHom t N := by
  dsimp only [smulHom, act]
  rw [Category.assoc, Category.assoc, act_hom, ← whisker_exchange_assoc,
    ← leftUnitor_inv_naturality_assoc]

variable [BraidedCategory C] [IsCommMonObj S]

/-- Left and right multiplication by a global section of a commutative algebra object agree. -/
@[reassoc]
lemma rightUnitor_inv_whiskerLeft_mul_eq (t : 𝟙_ C ⟶ S) :
    (ρ_ S).inv ≫ S ◁ t ≫ μ[S] = (λ_ S).inv ≫ t ▷ S ≫ μ[S] := by
  conv_lhs => rw [← IsCommMonObj.mul_comm S]
  rw [braiding_naturality_right_assoc, rightUnitor_inv_braiding_assoc]

/-- Multiplication by a global section is `S`-linear, since `S` is commutative. -/
lemma act_smulHom (t : 𝟙_ C ⟶ S) (M : Mod C S) :
    act M.X ≫ smulHom t M = S ◁ smulHom t M ≫ act M.X := by
  dsimp only [smulHom, act]
  rw [leftUnitor_inv_naturality_assoc, whisker_exchange_assoc, MonoidalCategory.whiskerLeft_comp,
    MonoidalCategory.whiskerLeft_comp, Category.assoc, Category.assoc, ModObj.mul_smul_self_flip]
  calc (λ_ (S ⊗ M.X)).inv ≫ t ▷ (S ⊗ M.X) ≫ (α_ S S M.X).inv ≫ μ[S] ▷ M.X ≫ γ[S,M.X] =
        ((λ_ S).inv ≫ t ▷ S ≫ μ[S]) ▷ M.X ≫ γ[S,M.X] := by monoidal
    _ = ((ρ_ S).inv ≫ S ◁ t ≫ μ[S]) ▷ M.X ≫ γ[S,M.X] := by
        rw [rightUnitor_inv_whiskerLeft_mul_eq]
    _ = _ := by monoidal

/-- Multiplication by a global section `t : 𝟙 ⟶ S` on `S`-module objects, as a natural
endomorphism of the identity functor of `Mod C S`. -/
noncomputable def smulNatTrans (t : 𝟙_ C ⟶ S) : 𝟭 (Mod C S) ⟶ 𝟭 (Mod C S) where
  app M := homMk (smulHom t M) (act_smulHom t M)
  naturality _ _ f := Mod.hom_ext _ _ (smulHom_naturality t f).symm

/-- Multiplication by `t` on `M` is `m ↦ t m`, i.e. `M ≅ 𝟙 ⊗ M ⟶ S ⊗ M ⟶ M`. -/
lemma smulNatTrans_app_hom (t : 𝟙_ C ⟶ S) (M : Mod C S) :
    ((smulNatTrans t).app M).hom = (λ_ M.X).inv ≫ t ▷ M.X ≫ γ[S,M.X] :=
  rfl

/-- Multiplication by `t` on a relative tensor product `M ⊗_S N` is `M ⊗_S (t •)`. -/
lemma smulNatTrans_app_tensor [HasCoequalizers C]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] (t : 𝟙_ C ⟶ S) (M N : Mod C S) :
    (smulNatTrans t).app (M ⊗ N) = M ◁ (smulNatTrans t).app N := by
  refine Mod.hom_ext _ _ ?_
  rw [← cancel_epi (tensorObjπ M N), tensorObjπ_whiskerLeft, smulNatTrans_app_hom,
    smulNatTrans_app_hom, leftUnitor_inv_naturality_assoc, whisker_exchange_assoc,
    whiskerLeft_tensorπ_smul]
  have h : (ρ_ M.X).inv ≫ M.X ◁ t ≫ (β_ M.X S).hom ≫ γ[S,M.X] =
      (λ_ M.X).inv ≫ t ▷ M.X ≫ γ[S,M.X] := by
    rw [braiding_naturality_right_assoc, rightUnitor_inv_braiding_assoc]
  symm
  calc M.X ◁ ((λ_ N.X).inv ≫ t ▷ N.X ≫ γ[S,N.X]) ≫ tensorObjπ M N =
        ((ρ_ M.X).inv ≫ M.X ◁ t) ▷ N.X ≫ ((α_ M.X S N.X).hom ≫ M.X ◁ γ[S,N.X]) ≫
          tensorObjπ M N := by monoidal
    _ = ((ρ_ M.X).inv ≫ M.X ◁ t ≫ (β_ M.X S).hom ≫ γ[S,M.X]) ▷ N.X ≫ tensorObjπ M N := by
        rw [← tensorObjπ_condition]
        simp only [comp_whiskerRight, Category.assoc]
    _ = ((λ_ M.X).inv ≫ t ▷ M.X ≫ γ[S,M.X]) ▷ N.X ≫ tensorObjπ M N := by rw [h]
    _ = _ := by monoidal

end CategoryTheory.Mod
