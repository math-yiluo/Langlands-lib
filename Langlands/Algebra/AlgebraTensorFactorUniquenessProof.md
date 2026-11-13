# Uniqueness of the simple factors of an external tensor product

Module `Langlands.Algebra.AlgebraTensorFactorUniquenessProof`. The theorem
`Langlands.algebraTensorFactorUniqueness` proves exactly the published
`Langlands.AlgebraTensorFactorUniquenessStatement`, with independent universe
parameters `u₁`, `u₂`, `v₁`, `v₂`, `w₁`, `w₂`.

For unital complex algebras `A₁`, `A₂`, let `V₁`, `W₁` be finite-dimensional
simple `A₁`-modules and `V₂`, `W₂` finite-dimensional simple `A₂`-modules, with
the compatible complex scalar structures in the statement. A complex-linear
equivalence between `V₁ ⊗ V₂` and `W₁ ⊗ W₂` intertwining their specified
`A₁ ⊗ A₂` actions yields an `A₁`-linear equivalence `V₁ ≃ W₁` and an
`A₂`-linear equivalence `V₂ ≃ W₂`.

## Provenance and scope

The target is imported unchanged from
`Langlands.Algebra.AlgebraTensorSimpleModuleStatements`. Its paired Markdown
records the provenance in Renard, *Représentations des groupes réductifs
p-adiques*, edition dated 9 July 2026, III.1.14 Scholium, printed pp.66–67 /
PDF pp.72–73, and explains the use of the tensor product algebra for the
source's external tensor action.

This unit implements a coefficient extraction and Schur proof of that published
uniqueness statement. Its helper lemmas are internal linear-algebra consequences
of Mathlib's tensor product, basis, duality and simple-module results. They
introduce no additional literature-derived definitions or statements. The
external-simplicity and existence conjuncts, and the final combined Scholium,
are separate proof units.

## Extracting a left-factor isomorphism

The internal lemma `Langlands.AlgebraTensorUniqueness.left_factor` works over
an arbitrary field `K`. Suppose `V` and `W` are simple modules over a unital
`K`-algebra `A`, `Y` is a nontrivial `K`-vector space, and
`e : V ⊗[K] Y ≃ₗ[K] W ⊗[K] Z` commutes with the left `A` action.

Choose nonzero `v ∈ V` and `y ∈ Y`. A functional taking `y` to `1` shows that
`v ⊗ y` is nonzero by contracting its right factor. Consequently its image
under `e` is nonzero. Express that image using
`TensorProduct.equivFinsuppOfBasisRight` for a basis of `Z`. At least one
coefficient is nonzero.

The corresponding coefficient projection `W ⊗ Z → W` is `A`-linear:
on pure tensors it is multiplication by a `K` scalar, which commutes with the
`A` action by the scalar-tower hypotheses; tensor induction handles sums.
Insertion `x ↦ x ⊗ y` is also `A`-linear. Composing insertion, the given
intertwiner regarded as an `A`-linear map, and coefficient projection produces
`f : V →ₗ[A] W`. Its chosen coefficient at `v` proves `f ≠ 0`.
Schur's lemma, `LinearMap.bijective_of_ne_zero`, makes `f` bijective.
`LinearEquiv.ofBijective` supplies the required isomorphism.

## Applying the lemma to both factors

The helper `left_action` identifies the published composite action of
`a₁ ⊗ 1` with the natural left `A₁` action on the tensor product.
The helper `comm_right_action` identifies the action of `1 ⊗ a₂`, after
applying `TensorProduct.comm`, with the left `A₂` action on the swapped tensor
product. Both identities follow from the pure-tensor action formula and
tensor induction.

For the first conclusion, specialize the given intertwining equation to
`a₁ ⊗ 1`, use `left_action`, and apply `left_factor` to `e`. Simplicity of
`V₂` supplies its required nontriviality.

For the second, conjugate `e` by the tensor commutativity equivalences to
obtain `e' : V₂ ⊗ V₁ ≃ₗ[ℂ] W₂ ⊗ W₁`. Specializing the original equation
to `1 ⊗ a₂` and using `comm_right_action` proves that `e'` commutes with
the left `A₂` action. Apply `left_factor` to `e'`; simplicity of `V₁`
supplies nontriviality of the new right source factor.

The generic extraction argument needs no finite-dimensionality or algebraic
closedness. The final theorem retains all the hypotheses of the exact
published complex, finite-dimensional target.
