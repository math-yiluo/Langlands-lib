/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.HomCongr

/-! # Invertibility of the counit composite of an internal-Hom mate

Source: Stacks Project, Tags 079W and 08DJ, with the Yoneda argument made explicit.
(blueprint: lem-pc-internal-hom-counit-mate-iso).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe uC uD vC vD

open CategoryTheory CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory

/-- The evaluation mate of a tensor-preserving left adjoint becomes invertible
when its second argument is a right-adjoint image and one applies the counit.
Source: Stacks Project, Tags 079W and 08DJ, the internal adjunction argument
(blueprint: lem-pc-internal-hom-counit-mate-iso).

Proof: For a test object A, transpose maps into the source by tensor-Hom on C,
then by F adjoint to R, and precompose by t.inv. Transpose maps into the target
by F adjoint to R and tensor-Hom on D. Both chains are bijections to maps
F(A) tensor F(M) to E. Naturality of the adjunction bijections and t, followed
by the defining mate equation, identifies postcomposition with the counit
composite with the identity under these chains. Yoneda detects invertibility. -/
theorem internalHomCounitMate_isIso
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [MonoidalCategory C] [MonoidalCategory D]
    (H : Cᵒᵖ × C ⥤ C) (J : Dᵒᵖ × D ⥤ D)
    (F : C ⥤ D) (R : D ⥤ C) (a : F ⊣ R)
    (bC : ∀ K : C, tensorRight K ⊣ (Functor.curry.obj H).obj (op K))
    (bD : ∀ K : D, tensorRight K ⊣ (Functor.curry.obj J).obj (op K))
    (t : tensor C ⋙ F ≅ F.prod F ⋙ tensor D)
    (γ : H ⟶ F.op.prod F ⋙ J ⋙ R)
    (hγ : ∀ K L : C,
      (a.homEquiv (H.obj (op K, L)) (J.obj (op (F.obj K), F.obj L))).symm
        (γ.app (op K, L)) =
      (bD (F.obj K)).homEquiv (F.obj (H.obj (op K, L))) (F.obj L)
        (t.inv.app (H.obj (op K, L), K) ≫ F.map ((bC K).counit.app L)))
    (M : C) (E : D) :
    IsIso (γ.app (op M, R.obj E) ≫
      R.map (J.map (X := (op (F.obj M), F.obj (R.obj E)))
        (Y := (op (F.obj M), E)) ((𝟙 (F.obj M)).op, a.counit.app E))) := by
  let c := γ.app (op M, R.obj E) ≫
    R.map (J.map (X := (op (F.obj M), F.obj (R.obj E)))
      (Y := (op (F.obj M), E)) ((𝟙 (F.obj M)).op, a.counit.app E))
  apply isIso_of_yoneda_map_bijective
  intro A
  let e₁ := ((bC M).homEquiv A (R.obj E)).symm.trans
    ((a.homEquiv (A ⊗ M) E).symm.trans
      (Iso.homCongr (t.app (A, M)) (Iso.refl E)))
  let e₂ := ((a.homEquiv A (J.obj (op (F.obj M), E))).symm).trans
    ((bD (F.obj M)).homEquiv (F.obj A) E).symm
  have hc (q : A ⟶ H.obj (op M, R.obj E)) : e₂ (q ≫ c) = e₁ q := by
    dsimp only [e₁, e₂, Equiv.trans_apply, c]
    rw [← Category.assoc, a.homEquiv_naturality_right_symm, a.homEquiv_naturality_left_symm]
    dsimp only [Functor.prod_obj, Functor.op_obj]
    rw [hγ M (R.obj E)]
    rw [Category.assoc]
    change ((bD (F.obj M)).homEquiv (F.obj A) E).symm
      (F.map q ≫
        (bD (F.obj M)).homEquiv _ _
          (t.inv.app (H.obj (op M, R.obj E), M) ≫ F.map ((bC M).counit.app _)) ≫
        ((Functor.curry.obj J).obj (op (F.obj M))).map (a.counit.app E)) = _
    rw [← Category.assoc, (bD (F.obj M)).homEquiv_naturality_right_symm,
      (bD (F.obj M)).homEquiv_naturality_left_symm, Equiv.symm_apply_apply]
    have ht := t.inv.naturality (X := (A, M)) (Y := (H.obj (op M, R.obj E), M))
      (q, 𝟙 M)
    dsimp at ht
    simp only [Functor.map_id] at ht
    change (F.map q ⊗ₘ 𝟙 (F.obj M)) ≫ _ = _ at ht
    simp only [Iso.homCongr_apply, Iso.refl_hom, Category.comp_id]
    simp only [← Category.assoc]
    change (((F.map q ▷ F.obj M) ≫ t.inv.app (H.obj (op M, R.obj E), M)) ≫
      F.map ((bC M).counit.app (R.obj E))) ≫ a.counit.app E =
      t.inv.app (A, M) ≫ _
    rw [← tensorHom_id, ht]
    simp only [Adjunction.homEquiv_symm_apply, Category.assoc,
      tensorHom_id]
    change t.inv.app (A, M) ≫ F.map (q ▷ M) ≫
      F.map ((bC M).counit.app (R.obj E)) ≫ a.counit.app E =
      t.inv.app (A, M) ≫ (F.map (q ▷ M ≫ (bC M).counit.app (R.obj E)) ≫
        a.counit.app E)
    simp only [Functor.map_comp, Category.assoc]
  have he : (fun q : A ⟶ H.obj (op M, R.obj E) ↦ q ≫ c) = e₁.trans e₂.symm := by
    funext q
    apply e₂.injective
    change e₂ (q ≫ c) = e₂ (e₂.symm (e₁ q))
    rw [Equiv.apply_symm_apply]
    exact hc q
  change Function.Bijective (fun q : A ⟶ H.obj (op M, R.obj E) ↦ q ≫ c)
  rw [he]
  exact (e₁.trans e₂.symm).bijective

end CategoryTheory
