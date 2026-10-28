/-
Copyright (c) 2025 Matthew Jasper. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Jasper

Derived by Worker 288 (2026), with the target specification by Worker 98:
state inverse laws for the published adaptations of Imperial FLT,
commit 923d45174c500aa1d994ba973bac38ea39eacbf7,
FLT/DedekindDomain/FiniteAdeleRing/TensorRestrictedProduct.lean:234-244,
with module hypotheses from lines 28-32 and 102. The new grouped Prop target
is an internal consequence suggested by Mathlib's LinearEquiv inverse laws;
the original does not state this grouped target. Import the actual canonical
maps and equivalences unchanged, and assert their laws without a proof.
The upstream license is retained at licenses/ImperialCollegeLondon-FLT/LICENSE.
-/
import Langlands.LinearAlgebra.RestrictedProduct.TensorEquiv

/-!
# Inverse-law target for the restricted-product tensor equivalences

The `R`-linear and `M`-linear clauses quantify their data separately. Each
asserts both inverse identities between the canonical forward map and the
published equivalence's `.symm`, on arbitrary elements of the actual domain
and tensor-image restricted-product codomain.
-/

universe uR uM uι uN

open scoped TensorProduct

namespace RestrictedProduct

/-- Both inverse laws for each published tensor equivalence and its canonical
forward map. The first clause allows general modules; the second retains the
algebra hypotheses and left-factor `M`-actions. All data and instances are
quantified inside this proposition. This definition states the target only. -/
def TensorEquivInverseLaws : Prop :=
  (∀ (R : Type uR) (M : Type uM) [CommRing R] [AddCommGroup M] [Module R M]
      [Module.FinitePresentation R M] [Module.Flat R M]
      (ι : Type uι) (N : ι → Type uN) [∀ i, AddCommGroup (N i)]
      [∀ i, Module R (N i)] (ℱ : Filter ι) (L : ∀ i, Submodule R (N i)),
      let e := lTensorEquiv R M N ℱ L
      let f := lTensor R M N ℱ L
      (∀ x : M ⊗[R] (Πʳ i, [N i, L i]_[ℱ]), e.symm (f x) = x) ∧
      (∀ y : Πʳ i, [M ⊗[R] N i, rangeLTensor R M N L i]_[ℱ],
        f (e.symm y) = y)) ∧
  (∀ (R : Type uR) (M : Type uM) [CommRing R] [CommRing M] [Algebra R M]
      (ι : Type uι) (N : ι → Type uN) [∀ i, Ring (N i)] [∀ i, Algebra R (N i)]
      (L : ∀ i, Submodule R (N i)) (ℱ : Filter ι)
      [Module.Flat R M] [Module.FinitePresentation R M],
      let e := lTensorEquivLeft R M N L ℱ
      let f := lTensorLeft R M N ℱ L
      (∀ x : M ⊗[R] (Πʳ i, [N i, L i]_[ℱ]), e.symm (f x) = x) ∧
      (∀ y : Πʳ i, [M ⊗[R] N i, rangeLTensorLeft R M N L i]_[ℱ],
        f (e.symm y) = y))

end RestrictedProduct
