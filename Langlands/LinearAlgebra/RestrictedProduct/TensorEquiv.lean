/-
Copyright (c) 2025 Matthew Jasper. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Jasper

Modified by Worker 217 (2026): adapt the equivalences and coordinate formulas
of Imperial FLT, commit 923d45174c500aa1d994ba973bac38ea39eacbf7,
FLT/DedekindDomain/FiniteAdeleRing/TensorRestrictedProduct.lean:234-257, with
the hypotheses of lines 28-32 and 102 and of lines 240-244, into one standalone
module. The bijectivity proofs `lTensor_bijective` and `lTensorLeft_bijective`
of the source are not reproduced: both equivalences instead take the second and
third clauses of the already published theorem
`RestrictedProduct.tensorRestrictedProductComparison_proof`. The four universes
are named explicitly, the unused section variable `S` is dropped, and the
module-system keywords are removed. The docstrings say "finitely presented
flat" instead of "finite flat", and the docstring of `lTensorEquivLeft` names
`lTensorLeft` instead of `lTensor`. `lTensorEquiv_tmul` is proved by rewriting
with `LinearEquiv.ofBijective_apply` and `lTensor_tmul` instead of `rfl`, and
`lTensorEquivLeft_tmul` by `LinearEquiv.ofBijective_apply` and
`lTensorLeft_tmul` instead of `simp`. The upstream license is retained at
licenses/ImperialCollegeLondon-FLT/LICENSE.
-/
import Langlands.LinearAlgebra.RestrictedProduct.TensorProof

/-!
# Tensor product distributing over a restricted product: equivalences

For a finitely presented flat `R`-module `M` and a restricted product of
`R`-modules `N i` relative to submodules `L i`, the natural `R`-linear map
`M ⊗_R ∏'ᵢ [N i, L i] → ∏'ᵢ [M ⊗_R N i, M ⊗_R L i]` is an `R`-linear
equivalence. When `M` is moreover a commutative `R`-algebra and the `N i` are
`R`-algebras, the natural `M`-linear map is an `M`-linear equivalence.
-/

universe uR uM uι uN

namespace RestrictedProduct

open TensorProduct

section module

variable (R : Type uR) (M : Type uM) [CommRing R] [AddCommGroup M] [Module R M]
  {ι : Type uι} (N : ι → Type uN) [∀ i, AddCommGroup (N i)]
  [∀ i, Module R (N i)]

variable (ℱ : Filter ι) (L : ∀ i, Submodule R (N i))

variable [Module.FinitePresentation R M] [Module.Flat R M]

/-- The `R`-linear isomorphism given by `lTensor` when `M` is a finitely presented flat
`R`-module. -/
noncomputable def lTensorEquiv :
    M ⊗[R] Πʳ i, [N i, L i]_[ℱ] ≃ₗ[R] Πʳ i, [M ⊗[R] N i, rangeLTensor R M N L i]_[ℱ] :=
  LinearEquiv.ofBijective (lTensor R M N ℱ L)
    (tensorRestrictedProductComparison_proof.{uR, uM, uι, uN}.2.1 R M ι N L ℱ)

@[simp]
lemma lTensorEquiv_tmul (m : M) (f : Πʳ i, [N i, L i]_[ℱ]) (i : ι) :
    lTensorEquiv R M N ℱ L (m ⊗ₜ f) i = m ⊗ₜ (f i) := by
  rw [lTensorEquiv, LinearEquiv.ofBijective_apply, lTensor_tmul]

end module

/-- The `M`-linear isomorphism given by `lTensorLeft` when `M` is a finitely presented flat
`R`-module. -/
noncomputable def lTensorEquivLeft (R : Type uR) (M : Type uM) [CommRing R] [CommRing M]
    [Algebra R M] {ι : Type uι} (N : ι → Type uN) [∀ i, Ring (N i)] [∀ i, Algebra R (N i)]
    (L : ∀ i, Submodule R (N i)) (ℱ : Filter ι) [Module.Flat R M]
    [Module.FinitePresentation R M] :
    M ⊗[R] Πʳ i, [N i, L i]_[ℱ] ≃ₗ[M] Πʳ i, [M ⊗[R] N i, rangeLTensorLeft R M N L i]_[ℱ] :=
  LinearEquiv.ofBijective (lTensorLeft R M N ℱ L)
    (tensorRestrictedProductComparison_proof.{uR, uM, uι, uN}.2.2 R M ι N L ℱ)

@[simp]
lemma lTensorEquivLeft_tmul (R : Type uR) (M : Type uM) [CommRing R] [CommRing M]
    [Algebra R M] {ι : Type uι} (N : ι → Type uN) [∀ i, Ring (N i)] [∀ i, Algebra R (N i)]
    (L : ∀ i, Submodule R (N i)) (ℱ : Filter ι) [Module.Flat R M]
    [Module.FinitePresentation R M] (m : M) (f : Πʳ i, [N i, L i]_[ℱ]) (i : ι) :
    lTensorEquivLeft R M N L ℱ (m ⊗ₜ f) i = m ⊗ₜ (f i) := by
  rw [lTensorEquivLeft, LinearEquiv.ofBijective_apply, lTensorLeft_tmul]

end RestrictedProduct
