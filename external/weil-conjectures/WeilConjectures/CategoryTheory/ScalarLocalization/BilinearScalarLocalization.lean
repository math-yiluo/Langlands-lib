/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalization
public import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Tactic.Ring

/-! # Bilinear functors on raw scalar localizations

Source: module base change, Stacks 00CV and 00CX; the rational tensor paragraph of
blueprint `prose-03-02`.
(blueprint: lem-sf-bilinear-functor-scalar-localization).
-/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory TensorProduct
namespace CategoryTheory.ScalarLocalization

section TensorLocalization
set_option backward.defeqAttrib.useBackward false
variable {D : Type*} [Category* D] [Preadditive D]
  (A : Type*) [CommRing A] [Linear A D] (p : A) (B : D × D ⥤ D)
  (β : ∀ M M' N N' : D, (M ⟶ M') →ₗ[A] (N ⟶ N') →ₗ[A]
    (B.obj (M, N) ⟶ B.obj (M', N')))
  (hβ : ∀ (M M' N N' : D) (a : M ⟶ M') (b : N ⟶ N'),
    β M M' N N' a b = B.map (Prod.mkHom a b))

private def tensorLocalizedAction (M M' N N' : ScalarLocalization A D p) :
    (Localization.Away p ⊗[A] (M.obj ⟶ M'.obj)) →ₗ[Localization.Away p]
      (Localization.Away p ⊗[A] (N.obj ⟶ N'.obj)) →ₗ[Localization.Away p]
      (Localization.Away p ⊗[A] (B.obj (M.obj, N.obj) ⟶ B.obj (M'.obj, N'.obj))) :=
  TensorProduct.curry
    (((TensorProduct.lift (β M.obj M'.obj N.obj N'.obj)).baseChange
      (Localization.Away p)).comp
        (AlgebraTensorModule.distribBaseChange A (Localization.Away p)
          (M.obj ⟶ M'.obj) (N.obj ⟶ N'.obj)).symm.toLinearMap)

include hβ

private theorem tensorLocalizedAction_tmul (M M' N N' : ScalarLocalization A D p)
    (a : M.obj ⟶ M'.obj) (b : N.obj ⟶ N'.obj) (x y : Localization.Away p) :
    tensorLocalizedAction A p B β M M' N N' (x ⊗ₜ[A] a) (y ⊗ₜ[A] b) =
      (x * y) ⊗ₜ[A] B.map (Prod.mkHom a b) := by
  simp [tensorLocalizedAction, hβ]

attribute [local irreducible] tensorLocalizedAction

private theorem tensorLocalizedAction_comp (M M' M'' N N' N'' : ScalarLocalization A D p)
    (a : M ⟶ M') (a' : M' ⟶ M'') (b : N ⟶ N') (b' : N' ⟶ N'') :
    tensorLocalizedAction A p B β M M'' N N'' (a ≫ a') (b ≫ b') =
      ScalarLocalization.composition A D p _ _ _
        (tensorLocalizedAction A p B β M' M'' N' N'' a' b')
        (tensorLocalizedAction A p B β M M' N N' a b) := by
  change tensorLocalizedAction A p B β M M'' N N''
    (ScalarLocalization.composition A D p _ _ _ a' a)
    (ScalarLocalization.composition A D p _ _ _ b' b) = _
  change Localization.Away p ⊗[A] (M.obj ⟶ M'.obj) at a
  change Localization.Away p ⊗[A] (M'.obj ⟶ M''.obj) at a'
  change Localization.Away p ⊗[A] (N.obj ⟶ N'.obj) at b
  change Localization.Away p ⊗[A] (N'.obj ⟶ N''.obj) at b'
  induction a using TensorProduct.inductionOn with
  | add a c ha hc => simp only [map_add, LinearMap.add_apply, ha, hc]
  | tmul x a =>
    induction a' using TensorProduct.inductionOn with
    | add a' c ha hc => simp only [map_add, LinearMap.add_apply, ha, hc]
    | tmul x' a' =>
      induction b using TensorProduct.inductionOn with
      | add b c hb hc => simp only [map_add, hb, hc]
      | tmul y b =>
        induction b' using TensorProduct.inductionOn with
        | add b' c hb hc => simp only [map_add, LinearMap.add_apply, hb, hc]
        | tmul y' b' =>
          simp only [ScalarLocalization.composition_tmul,
            tensorLocalizedAction_tmul A p B β hβ]
          rw [show B.map (Prod.mkHom (a ≫ a') (b ≫ b')) =
            B.map (Prod.mkHom a b) ≫ B.map (Prod.mkHom a' b') from
              B.map_comp (Prod.mkHom a b) (Prod.mkHom a' b')]
          congr 1
          ring

private def tensorLocalizedFunctor :
    ScalarLocalization A D p × ScalarLocalization A D p ⥤ ScalarLocalization A D p where
  obj MN := ⟨B.obj (MN.1.obj, MN.2.obj)⟩
  map {MN PQ} f := tensorLocalizedAction A p B β MN.1 PQ.1 MN.2 PQ.2 f.1 f.2
  map_id MN := by
    change tensorLocalizedAction A p B β MN.1 MN.1 MN.2 MN.2
      (1 ⊗ₜ[A] 𝟙 _) (1 ⊗ₜ[A] 𝟙 _) = _
    rw [tensorLocalizedAction_tmul A p B β hβ, one_mul]
    congr 1
    exact B.map_id _
  map_comp {MN PQ RS} f g :=
    tensorLocalizedAction_comp A p B β hβ MN.1 PQ.1 RS.1 MN.2 PQ.2 RS.2 f.1 g.1 f.2 g.2

/-- A bilinear arrow action extends uniquely to the raw scalar-localized category,
keeping the original output on objects and multiplying the two scalar factors.
Source: module base change, Stacks 00CV and 00CX; the rational tensor paragraph of
blueprint `prose-03-02`.
(blueprint: lem-sf-bilinear-functor-scalar-localization).

Proof: lift the integral bilinear action to the tensor product, base change the
resulting linear map, distribute base change across both inputs and curry. The
pure-tensor formula follows from these constructions. Four tensor inductions
reduce preservation of composition to the original functor law and the equality
(x*x')*(y*y')=(x'*y')*(x*y). Linearity handles zero and sum cases. The identity
formula uses the original identity law. Assemble this action into a functor.
For uniqueness, functor extensionality supplies the prescribed object transports;
two tensor inductions reduce its arrow equation to the given HEq generator
formula. Bilinearity of the competing action and of composition handles zeros
and sums. This proof also covers zero rings and localization at zero. -/
theorem bilinearFunctor_existsUnique :
    ∃! F : ScalarLocalization A D p × ScalarLocalization A D p ⥤ ScalarLocalization A D p,
      (∀ MN, F.obj MN = ⟨B.obj (MN.1.obj, MN.2.obj)⟩) ∧
      (∀ M M' N N' : ScalarLocalization A D p,
        ∃ b : (M ⟶ M') →ₗ[Localization.Away p] (N ⟶ N') →ₗ[Localization.Away p]
            (F.obj (M, N) ⟶ F.obj (M', N')),
          (∀ a b', F.map (Prod.mkHom a b') = b a b') ∧
          ∀ (a : M.obj ⟶ M'.obj) (b' : N.obj ⟶ N'.obj) (c d : Localization.Away p),
            HEq (b (c ⊗ₜ[A] a) (d ⊗ₜ[A] b'))
              ((c * d) ⊗ₜ[A] B.map (Prod.mkHom a b'))) := by
  let F := tensorLocalizedFunctor A p B β hβ
  refine ⟨F, ⟨fun _ ↦ rfl, ?_⟩, ?_⟩
  · intro M M' N N'
    refine ⟨tensorLocalizedAction A p B β M M' N N', fun _ _ ↦ rfl, ?_⟩
    intro a b c d
    exact heq_of_eq (tensorLocalizedAction_tmul A p B β hβ M M' N N' a b c d)
  · intro G hG
    refine CategoryTheory.Functor.ext hG.1 ?_
    intro MN PQ f
    obtain ⟨γ, hγ, pγ⟩ := hG.2 MN.1 PQ.1 MN.2 PQ.2
    change G.map (Prod.mkHom f.1 f.2) = _
    rw [hγ]
    change γ f.1 f.2 = _ ≫ tensorLocalizedAction A p B β MN.1 PQ.1 MN.2 PQ.2 f.1 f.2 ≫ _
    generalize f.1 = a, f.2 = b
    change Localization.Away p ⊗[A] (MN.1.obj ⟶ PQ.1.obj) at a
    change Localization.Away p ⊗[A] (MN.2.obj ⟶ PQ.2.obj) at b
    induction a using TensorProduct.inductionOn with
    | tmul c a =>
      induction b using TensorProduct.inductionOn with
      | tmul d b =>
        apply (conj_eqToHom_iff_heq _ _ (hG.1 MN) (hG.1 PQ)).2
        exact (pγ a b c d).trans
          (heq_of_eq (tensorLocalizedAction_tmul A p B β hβ MN.1 PQ.1 MN.2 PQ.2
            a b c d).symm)
      | add a b ha hb =>
        simp only [map_add]
        erw [Preadditive.add_comp, Preadditive.comp_add]
        exact congrArg₂ (· + ·) ha hb
    | add a b ha hb =>
      simp only [map_add, LinearMap.add_apply]
      erw [Preadditive.add_comp, Preadditive.comp_add]
      exact congrArg₂ (· + ·) ha hb

end TensorLocalization

end CategoryTheory.ScalarLocalization
