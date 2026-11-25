/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.ClosedScalarHom.ClosedScalarHomComparison
/-! # Composition of the five closed-Hom bijections -/
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u₁ v₁ u₂ v₂ u₃ v₃
open CategoryTheory Opposite WeilConjectures
namespace CategoryTheory.ClosedScalarHom
variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
  {C : Type u₃} [Category.{v₃} C]
  {H : Aᵒᵖ × A ⥤ A} {I : Bᵒᵖ × B ⥤ B} {J : Cᵒᵖ × C ⥤ C}
  (S : CoefficientClosedStructure H) (T : CoefficientClosedStructure I)
  (V : CoefficientClosedStructure J)
  {F : A ⥤ B} {U : B ⥤ A} (adj : F ⊣ U)
  {G : B ⥤ C} {W : C ⥤ B} (adj' : G ⊣ W)
  (μ : S.tensor ⋙ F ≅ (F.prod F) ⋙ T.tensor)
  (ν : T.tensor ⋙ G ≅ (G.prod G) ⋙ V.tensor)
  (μ₀ : S.tensor ⋙ (F ⋙ G) ≅ ((F ⋙ G).prod (F ⋙ G)) ⋙ V.tensor)
  (hμ : ∀ X K, μ₀.hom.app (X, K) =
    G.map (μ.hom.app (X, K)) ≫ ν.hom.app (F.obj X, F.obj K))

include hμ in
/-- The five-Hom comparison for a composite tensor functor is the composite comparison.
Source: Stacks 07A6 and 0D6D (blueprint: lem-sfb-closed-scalar-hom-composition).
Proof: test with the source identity and expand the five bijections. The hom equivalence
of a composite adjunction is the composite hom equivalence. Naturality moves the first
scalar counit through the second tensor comparison; the two middle closed transposes
cancel. The tensor-composition hypothesis identifies the remaining middle map. -/
theorem composition (K : A) (N : C) :
    (iso S V (adj.comp adj') μ₀).hom.app (op K, N) =
      U.map ((iso T V adj' ν).hom.app (op (F.obj K), N)) ≫
        (iso S T adj μ).hom.app (op K, W.obj N) := by
  rw [← representing S T adj μ]
  change bijection S V (adj.comp adj') μ₀ _ K N (𝟙 _) = _
  dsimp only [bijection, Equiv.trans_apply]
  rw [Adjunction.comp_homEquiv]
  dsimp only [Equiv.trans_apply, Equiv.symm_trans_apply, Iso.homCongr,
    Equiv.coe_fn_mk, Iso.symm_inv, Iso.refl_hom]
  simp only [Category.comp_id]
  apply congrArg (S.transpose _ K (U.obj (W.obj N)))
  apply congrArg (adj.homEquiv _ _)
  have ht := adj.homEquiv_naturality_right_symm
    (𝟙 (U.obj (W.obj (J.obj (op (G.obj (F.obj K)), N)))))
    ((iso T V adj' ν).hom.app (op (F.obj K), N))
  simp only [Category.id_comp] at ht
  erw [ht]
  let Z := J.obj (op (G.obj (F.obj K)), N)
  let X := U.obj (W.obj Z)
  let t : F.obj X ⟶ W.obj Z := (adj.homEquiv X (W.obj Z)).symm (𝟙 _)
  let α := (iso T V adj' ν).hom.app (op (F.obj K), N)
  change (adj'.homEquiv _ N)
    (μ₀.hom.app (X, K) ≫ (V.transpose _ _ N).symm ((adj'.homEquiv _ Z).symm t)) =
      μ.hom.app (X, K) ≫ (T.transpose _ _ (W.obj N)).symm (t ≫ α)
  let := T.monoidal
  let := V.monoidal
  have hT : (T.transpose _ _ (W.obj N)).symm (t ≫ α) =
      T.tensor.map (Prod.mkHom t (𝟙 (F.obj K))) ≫
        (T.transpose _ _ (W.obj N)).symm α := by
    simpa [CoefficientClosedStructure.transpose, CoefficientClosedStructure.tensor,
      Prod.sectR, MonoidalCategory.tensorRight, MonoidalCategory.tensor,
      MonoidalCategory.curriedTensor, CategoryTheory.Functor.flip] using
      (T.adjunction (F.obj K)).homEquiv_naturality_left_symm t α
  have hα : α = T.transpose _ _ (W.obj N)
      ((adj'.homEquiv _ N) (ν.hom.app (W.obj Z, F.obj K) ≫
        (V.transpose _ _ N).symm ((adj'.homEquiv _ Z).symm (𝟙 _)))) := by
    dsimp only [α, iso, NatIso.ofComponents, component, bijection, Equiv.trans_apply,
      Iso.homCongr, Equiv.coe_fn_mk, Iso.symm_inv, Iso.refl_hom]
    simp only [Category.comp_id, Iso.app_hom]
    rfl
  rw [hT, hα, Equiv.symm_apply_apply]
  rw [← adj'.homEquiv_naturality_left]
  have ht' := adj'.homEquiv_naturality_left_symm t (𝟙 (W.obj Z))
  simp only [Category.comp_id] at ht'
  rw [ht']
  have hV : (V.transpose _ _ N).symm
      (G.map t ≫ (adj'.homEquiv (W.obj Z) Z).symm (𝟙 _)) =
      V.tensor.map (Prod.mkHom (G.map t) (𝟙 (G.obj (F.obj K)))) ≫
        (V.transpose _ _ N).symm ((adj'.homEquiv (W.obj Z) Z).symm (𝟙 _)) := by
    simpa [CoefficientClosedStructure.transpose, CoefficientClosedStructure.tensor,
      Prod.sectR, MonoidalCategory.tensorRight, MonoidalCategory.tensor,
      MonoidalCategory.curriedTensor, CategoryTheory.Functor.flip] using
      (V.adjunction (G.obj (F.obj K))).homEquiv_naturality_left_symm (G.map t)
        ((adj'.homEquiv (W.obj Z) Z).symm (𝟙 _))
  dsimp only [Functor.comp_obj, Prod.fst, Prod.snd]
  rw [hV, hμ]
  have hν := ν.hom.naturality (Prod.mkHom t (𝟙 (F.obj K)))
  dsimp only [Functor.comp_map, Functor.prod_map] at hν
  rw [G.map_id] at hν
  simp only [Category.assoc]
  rw [← reassoc_of% hν, adj'.homEquiv_naturality_left]
  rfl
end CategoryTheory.ClosedScalarHom
