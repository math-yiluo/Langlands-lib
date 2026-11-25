/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCupResolutionData
import WeilConjectures.AlgebraicGeometry.ModuleCupCosimplicialAW
public import Mathlib.Topology.Sheaves.Flasque
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.Embedding.IsSupported
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed

/-! # Flasque augmented resolutions with an Alexander–Whitney pairing

The statement supplies exact flasque complexes and a chain pairing; it does not
supply comparisons with injective resolutions or a pairing on cohomology.
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Flasque augmented resolutions admit a tensor chain pairing over the augmentations.
Source: Godement, Topologie algébrique et théorie des faisceaux, II §6,
canonical flasque resolutions and their Alexander–Whitney product.
(blueprint: lem-sc-module-cup-godement-aw)
Proof: form the augmented cosimplicial Godement resolution from products of stalks.
Its augmentation is exact on stalks. The cosimplicial terms are flasque because
restrictions forget coordinates, and its nonnegative unnormalized cochain complex
is an exact augmented resolution. The natural stalkwise tensor maps and the
Alexander–Whitney front/back faces give a bilinear map of total complexes. The
cosimplicial identities prove the signed Leibniz identity, making it a cochain map.
The degree-zero map is the ordinary tensor of coefficient sections under the
augmentations. All negative terms are zero, and the empty-space and zero-sheaf
cases use the same construction. -/
theorem moduleCup_godement_pairing (X : Scheme.{u}) (F G : X.Modules) :
    letI : MonoidalPreadditive X.Modules :=
      Classical.choice (SheafOfModules.tensorClosed X.sheaf).1
    ∃ (K L M : CochainComplex X.Modules ℤ)
      (a : (CochainComplex.singleFunctor X.Modules 0).obj F ⟶ K)
      (b : (CochainComplex.singleFunctor X.Modules 0).obj G ⟶ L)
      (c : (CochainComplex.singleFunctor X.Modules 0).obj (F ⊗ G) ⟶ M),
      QuasiIso a ∧ QuasiIso b ∧ QuasiIso c ∧
      K.IsStrictlyGE 0 ∧ L.IsStrictlyGE 0 ∧ M.IsStrictlyGE 0 ∧
      (∀ n : ℤ, TopCat.Sheaf.IsFlasque
        ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj (K.X n))) ∧
      (∀ n : ℤ, TopCat.Sheaf.IsFlasque
        ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj (L.X n))) ∧
      (∀ n : ℤ, TopCat.Sheaf.IsFlasque
        ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj (M.X n))) ∧
      ∃ t : HomologicalComplex.tensorObj K L ⟶ M,
        ∀ (V : X.Opens)
          (x : Γ(((CochainComplex.singleFunctor X.Modules 0).obj F).X 0, V))
          (y : Γ(((CochainComplex.singleFunctor X.Modules 0).obj G).X 0, V)),
          (t.f 0).val.app (op V)
            ((HomologicalComplex.ιTensorObj K L 0 0 0 (by simp)).val.app (op V)
              (tmulSection ((a.f 0).val.app (op V) x) ((b.f 0).val.app (op V) y))) =
            (c.f 0).val.app (op V) (tmulSection x y) := by
  let : MonoidalPreadditive X.Modules :=
    Classical.choice (SheafOfModules.tensorClosed X.sheaf).1
  have hinput := moduleCup_godement_cosimplicial_input X F G
  rcases hinput with ⟨A, B, C, a, b, c, μ, hinput⟩
  rcases hinput with ⟨ha, hb, hc, hA, hB, hC, hμ⟩
  have haw := moduleCup_cosimplicial_aw X A B C μ
  rcases haw with ⟨t, ht⟩
  refine ⟨moduleCup_cosimplicialComplex X A, moduleCup_cosimplicialComplex X B,
    moduleCup_cosimplicialComplex X C, a, b, c, ha, hb, hc, ?_, ?_, ?_,
    hA, hB, hC, t, ?_⟩
  · unfold moduleCup_cosimplicialComplex
    infer_instance
  · unfold moduleCup_cosimplicialComplex
    infer_instance
  · unfold moduleCup_cosimplicialComplex
    infer_instance
  · intro V x y
    have h := congrArg
      (fun (f : (moduleCup_cosimplicialComplex X A).X 0 ⊗
          (moduleCup_cosimplicialComplex X B).X 0 ⟶
          (moduleCup_cosimplicialComplex X C).X 0) ↦ f.app V
        (tmulSection ((a.f 0).val.app (op V) x) ((b.f 0).val.app (op V) y))) ht
    rw [Hom.comp_app, ConcreteCategory.comp_apply] at h
    exact h.trans (hμ V x y)

end AlgebraicGeometry.Scheme.Modules
