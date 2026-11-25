/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons
import WeilConjectures.AlgebraicGeometry.PullbackTensorUnitSection

/-! # Symmetry of the boundary pullback tensor comparison

Source: Stacks Project, Tags 01CA and 01CD.
(blueprint: lem-sc-boundary-pullback-tensor-braiding).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
universe u
noncomputable section

private theorem tensor_hom_ext {X : Scheme.{u}} {A B C : X.Modules}
    {f g : A ⊗ B ⟶ C}
    (h : ∀ (U : X.Opens) (s : Γ(A, U)) (t : Γ(B, U)),
      f.app U (tmulSection s t) = g.app U (tmulSection s t)) : f = g := by
  let := presheafMonoidalCategory X
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification A B).inv).mp
  apply ((PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).homEquiv (A.val ⊗ B.val) C).injective
  apply PresheafOfModules.hom_ext
  intro U
  ext z
  induction z using TensorProduct.inductionOn with
  | tmul s t => exact h U.unop s t
  | add z w hz hw => simp only [map_add, hz, hw]

/-- The transported pullback tensor comparison respects symmetry for arbitrary modules.

Source: Stacks Project, Tag 01CD, lemma-tensor-product-pullback, and Tag 01CA.
(blueprint: lem-sc-boundary-pullback-tensor-braiding).
Proof: first use the canonical Mathlib pullback comparison. On presheaf tensor
sections the proved pullback_δ_app_unit_tmulSection identifies the pullback of x tensor y
with the tensor of their pullbacks. The sheaf tensor braiding is induced by x tensor y mapping
to y tensor x. The two composites therefore agree on pure presheaf tensors;
bilinearity and the sheafification universal property give equality of the
sheaf morphisms. Equivalently one can check this after stalk base extension,
where it is the usual symmetry of tensor products of modules. Finally expand
boundaryPullbackTensorIso and use naturality of boundaryPullbackComparison on
the original braiding, and naturality of braiding on its two component
isomorphisms. Cancel the inverse component maps to obtain the displayed square.
No invertibility or closed immersion is used; zero modules and empty schemes
satisfy the same pure tensor computation. -/
theorem boundaryPullbackTensorIso_braiding {X Z : Scheme.{u}} (j : Z ⟶ X)
    (A B : X.Modules) :
    (tensorPullback j).map (β_ A B).hom ≫ (boundaryPullbackTensorIso j B A).hom =
      (boundaryPullbackTensorIso j A B).hom ≫
        (β_ ((tensorPullback j).obj A) ((tensorPullback j).obj B)).hom  := by
  classical
  have hb : (pullback j).map (β_ A B).hom ≫
      Functor.OplaxMonoidal.δ (pullback j) B A =
      Functor.OplaxMonoidal.δ (pullback j) A B ≫
        (β_ ((pullback j).obj A) ((pullback j).obj B)).hom := by
    let adj := pullbackPushforwardAdjunction j
    apply (adj.homEquiv _ _).injective
    apply tensor_hom_ext
    intro U s t
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    change (Functor.OplaxMonoidal.δ (pullback j) B A).app (j ⁻¹ᵁ U)
        (((pullback j).map (β_ A B).hom).app (j ⁻¹ᵁ U)
          (pullbackUnitApp j (A ⊗ B) U (tmulSection s t))) =
      (β_ ((pullback j).obj A) ((pullback j).obj B)).hom.app (j ⁻¹ᵁ U)
        ((Functor.OplaxMonoidal.δ (pullback j) A B).app (j ⁻¹ᵁ U)
          (pullbackUnitApp j (A ⊗ B) U (tmulSection s t)))
    have hn := congrArg (fun f ↦ f.app U (tmulSection s t))
      (adj.unit_naturality (β_ A B).hom)
    change ((pullback j).map (β_ A B).hom).app (j ⁻¹ᵁ U)
        (pullbackUnitApp j (A ⊗ B) U (tmulSection s t)) =
      pullbackUnitApp j (B ⊗ A) U ((β_ A B).hom.app U (tmulSection s t)) at hn
    rw [hn, braiding_hom_app_tmulSection, pullback_δ_app_unit_tmulSection,
      pullback_δ_app_unit_tmulSection, braiding_hom_app_tmulSection]
  simp only [boundaryPullbackTensorIso, Iso.trans_hom, tensorIso_hom,
    Iso.symm_hom, Functor.Monoidal.μIso_inv, Iso.app_hom, Iso.app_inv, Category.assoc]
  rw [← Category.assoc, (boundaryPullbackComparison j).hom.naturality]
  simp only [Category.assoc]
  rw [reassoc_of% hb]
  rw [BraidedCategory.braiding_naturality]

end
end AlgebraicGeometry.Scheme.Modules
