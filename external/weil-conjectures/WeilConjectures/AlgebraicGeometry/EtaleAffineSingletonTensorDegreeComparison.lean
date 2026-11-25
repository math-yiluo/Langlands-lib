/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeHomNormalization
import WeilConjectures.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeHom
import WeilConjectures.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeInverse

/-! # Degreewise affine singleton tensor comparison
Source: Stacks Project, Tag 03P2, affine tensor-product calculation.
(blueprint: new-etale-affine-singleton-tensor-degree-comparison).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

noncomputable section

/-- Affine pullback sections give canonical degree isomorphisms, with their pure-tensor
normalization, without asserting compatibility between different degrees.
Source: Stacks Project, Tag 03P2, affine-case identification before exactness;
Tags 01I9 and 01IA for the affine fibre-product and module calculations.
(blueprint: new-etale-affine-singleton-tensor-degree-comparison)

Proof: write A = Γ(U,O), B = Γ(W,O), M = Γ(U,U*F). Compare tensor pullback with
Mathlib pullback using their adjunctions to the same pushforward. This transports
quasi-coherence of U*F. The product of n+1 copies of W over U is affine, and its
functions are the indexed tensor product of n+1 copies of B over A, with the
k-th projection inducing the k-th tensor inclusion. Apply the affine pullback
sections formula to this product over U. Normalize composite pullback by its
unit equation; on m tensor the pure tensor b the resulting section is the product
of the pulled-back b(k) times the restriction of m. The outer product is indexed
by functions to Fin 1, so evaluation at its unique index is an isomorphism.
Apply ULift and invert this evaluation to obtain e. Tensor generators prove the
stated normalization and also make e unique. For an empty W the section groups
and tensors are zero; for n=0 this is the ordinary affine sections formula.
Fixed-degree form: (blueprint: new-etale-affine-singleton-tensor-degree-comparison-degree) -/
/- Fixed-degree affine tensor-section calculation. The geometric proof identifies the
degree-n affine fibre product with the indexed tensor power, applies the affine pullback
sections formula, and checks the displayed normalization on pure tensors; tensor
generators then extend it to all sections. (blueprint: new-etale-affine-singleton-
tensor-degree-comparison-degree) -/
theorem exists_singletonTensorDegreeComparison_degree
    (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent]
    (U W : X.Etale) (g : W ⟶ U) (hU : IsAffine U.left) (hW : IsAffine W.left)
    (n : ℕ) :
    ∃ e : (singletonTensorAmitsur X F U W g).X n ≅
      (singletonTensorCech X F U W g).X n,
      IsSingletonTensorDegreeComparison X F U W g n e := by
  obtain ⟨f, hf⟩ :=
    exists_singletonTensorDegreeComparison_hom X F U W g hU hW n
  obtain ⟨inv, hfi, hif⟩ :=
    exists_singletonTensorDegreeComparison_inverse X F U W g hU hW n f hf
  let e : (singletonTensorAmitsur X F U W g).X n ≅
      (singletonTensorCech X F U W g).X n :=
    { hom := f
      inv := inv
      hom_inv_id := hfi
      inv_hom_id := hif }
  exact ⟨e, hf⟩

/-- (blueprint: new-etale-affine-singleton-tensor-degree-comparison) -/
theorem exists_singletonTensorDegreeComparison
    (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent]
    (U W : X.Etale) (g : W ⟶ U) (hU : IsAffine U.left) (hW : IsAffine W.left) :
    ∃ e : ∀ n : ℕ, (singletonTensorAmitsur X F U W g).X n ≅
      (singletonTensorCech X F U W g).X n,
      ∀ n, IsSingletonTensorDegreeComparison X F U W g n (e n) := by
  choose e he using fun n ↦
    exists_singletonTensorDegreeComparison_degree X F U W g hU hW n
  exact ⟨e, he⟩

end
end AlgebraicGeometry.Scheme
