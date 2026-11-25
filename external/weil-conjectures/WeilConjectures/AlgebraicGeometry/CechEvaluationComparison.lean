/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import WeilConjectures.Topology.Sheaves.Cech
import WeilConjectures.Topology.Sheaves.CechComparison

/-! Comparison of the categorical and concrete Čech complexes after evaluation. -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def cechEvalIso
    {X : TopCat.{u}} {ι : Type u} {R : Type u} [Ring R]
    (U : ι → Opens X)
    (Q : (Opens X)ᵒᵖ ⥤ ((Opens X)ᵒᵖ ⥤ ModuleCat.{u} R)) (V : Opens X) :
    (((evaluation (Opens X)ᵒᵖ (ModuleCat.{u} R)).obj (op V)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj ((cechComplexFunctor U).obj Q) ≅
      (cechComplexFunctor U).obj
        (Q ⋙ (evaluation (Opens X)ᵒᵖ (ModuleCat.{u} R)).obj (op V)) := by
  let T := (evaluation (Opens X)ᵒᵖ (ModuleCat.{u} R)).obj (op V)
  refine HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ PreservesProduct.iso T
      (fun y : Fin (n + 1) → ι ↦ Q.obj (op (∏ᶜ fun l ↦ U (y l))))) ?_
  rintro n _ rfl
  apply TopCat.Presheaf.cechComplexFunctor_hom_ext U (Q ⋙ T)
  intro y
  change (PreservesProduct.iso T _).hom ≫
    ((cechComplexFunctor U).obj (Q ⋙ T)).d n (n + 1) ≫
      TopCat.Presheaf.cechComplexFunctorπ U (Q ⋙ T) (n + 1) y =
    T.map (((cechComplexFunctor U).obj Q).d n (n + 1)) ≫
      (PreservesProduct.iso T _).hom ≫
        TopCat.Presheaf.cechComplexFunctorπ U (Q ⋙ T) (n + 1) y
  rw [PreservesProduct.iso_hom, PreservesProduct.iso_hom]
  erw [piComparison_comp_π]
  erw [← T.map_comp, TopCat.Presheaf.cechComplexFunctor_d_π U Q]
  rw [TopCat.Presheaf.cechComplexFunctor_d_π U (Q ⋙ T)]
  simp only [Functor.map_sum, Functor.map_zsmul, Functor.map_comp,
    Preadditive.comp_sum, Preadditive.comp_zsmul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  congr 1
  erw [← Category.assoc, piComparison_comp_π]
  rfl


namespace TopCat.Presheaf

private lemma intersection_le_prod {X : TopCat.{u}} {ι : Type u}
    (U : ι → Opens X) (V : Opens X) {n : ℕ} (y : Fin (n + 1) → ι) :
    (⨅ l, U (y l) ⊓ V) ≤ ((⨅ l, U (y l)) ⨯ V) := by
  rw [CompleteLattice.prod_eq_inf]
  exact le_inf (le_iInf fun l ↦ (iInf_le _ l).trans inf_le_left)
    ((iInf_le _ 0).trans inf_le_right)

private lemma prod_le_intersection {X : TopCat.{u}} {ι : Type u}
    (U : ι → Opens X) (V : Opens X) {n : ℕ} (y : Fin (n + 1) → ι) :
    ((⨅ l, U (y l)) ⨯ V) ≤ (⨅ l, U (y l) ⊓ V) := by
  rw [CompleteLattice.prod_eq_inf]
  exact le_iInf fun l ↦ inf_le_inf (iInf_le _ l) le_rfl

private noncomputable def intersectCochainEquiv
    {X : TopCat.{u}} {ι : Type u} {R : Type u} [Ring R]
    (U : ι → Opens X) (P : (Opens X)ᵒᵖ ⥤ ModuleCat.{u} R) (V : Opens X) (n : ℕ) :
    CechCochain U
      (((prod.functor (C := Opens X)).op ⋙ Functor.opHom _ _ ⋙
        (Functor.whiskeringRight _ _ _).obj P) ⋙
        (evaluation (Opens X)ᵒᵖ (ModuleCat.{u} R)).obj (op V) ⋙
        forget₂ (ModuleCat.{u} R) AddCommGrpCat) n ≃+
    CechCochain (fun i ↦ U i ⊓ V) (P ⋙ forget₂ (ModuleCat.{u} R) AddCommGrpCat) n where
  toFun x y := P.map (homOfLE (intersection_le_prod U V y)).op (x y)
  invFun x y := P.map (homOfLE (prod_le_intersection U V y)).op (x y)
  left_inv x := funext fun y ↦ by
    dsimp only
    rw [map_map_apply P _ _ (𝟙 _), map_apply_self]
  right_inv x := funext fun y ↦ by
    dsimp only
    rw [map_map_apply P _ _ (𝟙 _), map_apply_self]
  map_add' x x' := funext fun y ↦ by
    exact map_add _ _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def intersectComplexIso
    {X : TopCat.{u}} {ι : Type u} {R : Type u} [Ring R]
    (U : ι → Opens X) (P : (Opens X)ᵒᵖ ⥤ ModuleCat.{u} R) (V : Opens X) :
    (cechComplex U).obj
      (((prod.functor (C := Opens X)).op ⋙ Functor.opHom _ _ ⋙
        (Functor.whiskeringRight _ _ _).obj P) ⋙
        (evaluation (Opens X)ᵒᵖ (ModuleCat.{u} R)).obj (op V) ⋙
        forget₂ (ModuleCat.{u} R) AddCommGrpCat) ≅
    (cechComplex (fun i ↦ U i ⊓ V)).obj
      (P ⋙ forget₂ (ModuleCat.{u} R) AddCommGrpCat) := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (intersectCochainEquiv U P V n).toAddCommGrpIso) ?_
  rintro n _ rfl
  refine AddCommGrpCat.ext fun x ↦ funext fun y ↦ ?_
  simp only [ConcreteCategory.comp_apply]
  change ((cechComplex (fun i ↦ U i ⊓ V)).obj
    (P ⋙ forget₂ (ModuleCat.{u} R) AddCommGrpCat)).d n (n + 1)
      (intersectCochainEquiv U P V n x) y =
    intersectCochainEquiv U P V (n + 1)
      (((cechComplex U).obj _).d n (n + 1) x) y
  rw [cechComplex_d_apply]
  change _ = P.map _ ((((cechComplex U).obj _).d n (n + 1) x) y)
  rw [cechComplex_d_apply]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_zsmul]
  change _ • P.map _ (P.map _ _) = _ • P.map _ (P.map _ _)
  congr 1
  let h := (homOfLE ((iInf_le_iInf_comp (fun i ↦ U i ⊓ V) y j.succAbove).trans
    (intersection_le_prod U V (y ∘ j.succAbove)))).op
  rw [map_map_apply P _ _ h]
  exact (map_map_apply P _ _ h _).symm



/-- Evaluating the categorical Čech complex of the intersection presheaf gives
 the concrete Čech complex for the family intersected with the evaluating open.

Source: blueprint `lemma-coherent-base-change-invertible-sheaves`, proof paragraph 1, Čech
coordinates. (blueprint: lem-pc-cech-evaluation-comparison)

Proof: In degree n, the categorical product is indexed by tuples
 a : Fin (n+1) → ι. Evaluation and forgetting scalars preserve this product.
Its a-th factor is P((∏ b, U(a b)) ∩ V), canonically identified with
P(⋂ b, (U(a b) ∩ V)); here Fin (n+1) is nonempty. The universal property
of the product identifies these factors with the dependent-function cochains
of the concrete complex. A coface deletes the corresponding tuple entry and
restricts along the inclusion of intersections in both constructions. Thus
these degreewise identifications commute with every coface and with their
alternating sums, giving an isomorphism of cochain complexes. This argument
also applies to empty opens, empty index types, and zero coefficient modules.
-/
theorem cech_evaluation_comparison
    {X : TopCat.{u}} {ι : Type u} {R : Type u} [Ring R]
    (U : ι → Opens X) (P : (Opens X)ᵒᵖ ⥤ ModuleCat.{u} R) (V : Opens X) :
    Nonempty
      ((((evaluation (Opens X)ᵒᵖ (ModuleCat.{u} R)).obj (op V) ⋙
            forget₂ (ModuleCat.{u} R) AddCommGrpCat).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
        ((CategoryTheory.cechComplexFunctor U).obj
          ((prod.functor (C := Opens X)).op ⋙ Functor.opHom _ _ ⋙
            (Functor.whiskeringRight _ _ _).obj P)) ≅
        (cechComplex (fun i ↦ U i ⊓ V)).obj
          (P ⋙ forget₂ (ModuleCat.{u} R) AddCommGrpCat)) := by
  let Q := (prod.functor (C := Opens X)).op ⋙ Functor.opHom _ _ ⋙
    (Functor.whiskeringRight _ _ _).obj P
  let T := (evaluation (Opens X)ᵒᵖ (ModuleCat.{u} R)).obj (op V)
  refine ⟨?_⟩
  exact ((forget₂ (ModuleCat.{u} R) AddCommGrpCat).mapHomologicalComplex
    (ComplexShape.up ℕ)).mapIso (cechEvalIso U Q V) ≪≫
      cechComplexFunctorIso U (Q ⋙ T) ≪≫ intersectComplexIso U P V

end TopCat.Presheaf
