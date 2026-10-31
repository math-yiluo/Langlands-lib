# Spectral steps for weak upper Jacquet bounds of induced representations

Author: Worker 828.

This module contains the spectral parts of the proof of
`Langlands.GLInductionWeakJacquetBoundsStatement`. They are: reading the
central spectrum of refined normalized induction off the inducing
representation, and relabelling along subgroup equalities. All are internal
helpers used by
`Langlands.Representation.Classification.InductionWeakJacquetBoundsAssembly`.
The extension of a generalized eigencharacter from a sub-monoid of a central
action to the whole action, `Langlands.exists_eigencharacter_extension`, is
in the separate module
`Langlands.Representation.Exponents.CentralEigencharacterExtensionProof`.

## Central spectrum of refined induction

In namespace `Langlands.Geometric`, for a commutative ring `F`, a block
shape `C` and `R : BlockRefinement C`:

- `leviEmbedding_blockScalarLevi_const`: the block scalar with constant
  value `a` embeds as the scalar matrix `GeneralLinear.scalar a`.
- `refinedBlockScalar C R`: the block scalars of `C`, as a homomorphism into
  the refined Levi `refinedLevi F C R`. Its value has underlying element
  `C.blockScalarLevi F a` (`refinedBlockScalar_val`). Membership holds because
  each block `a i` is the constant block scalar of `R i`.
- `isGeneralizedEigencharacter_of_normalizedRefinedInducedOf`: let `δ` be a
  character of the refined Levi that is trivial on `refinedBlockScalar C R`.
  If `χ` is a generalized eigencharacter of the block scalars of `C` acting on
  `normalizedRefinedInducedOf C R δ τ`, then `χ` is a generalized
  eigencharacter of `τ.comp (refinedBlockScalar C R)`. Proof: a nonzero
  generalized eigenfunction `f` has a point `x` with `f x ≠ 0`. Evaluation at
  `x` intertwines the two block-scalar actions. Block scalars are central in
  `C.Levi`, so right translation by `z` gives `f (x z) = f (z x)`. Covariance
  (`normalizedRefinedInducedOf_covariant`, with `δ z = 1`) gives
  `f (z x) = τ z (f x)`. The published `isGeneralizedEigencharacter_of_map_ne_zero`
  concludes.
- `isGeneralizedEigencharacter_of_normalizedRefinedInductionFunctorOf`: the
  same statement for the value of `normalizedRefinedInductionFunctorOf` on a
  smooth representation. Its topological instances on `F` are implicit
  arguments, so a caller's hypothesis fixes them. This avoids a mismatch
  between instance paths of the topological-ring structure.
- `isGeneralizedEigencharacter_subgroupEqualityFunctor`: relabelling a smooth
  representation along `h : H = K` with `subgroupEqualityFunctor` changes
  generalized eigencharacters only by composition with
  `(MulEquiv.subgroupCongr h).symm`. The proof is `subst h; rfl`.

In namespace `Langlands.PadicField.TopologicalData`:

- `refinedLeviBlock_refinedBlockScalar`: the `i`-th inner block of
  `refinedBlockScalar C R a` is the constant block scalar of `R i` with value
  `a i`.
- `refinedLeviModulus_refinedBlockScalar`: the actual refined modulus is
  trivial on these elements. By `refinedLeviModulus_apply` it is a product
  of block moduli, each trivial on scalars (`leviModulus_scalar`).
- `refinedLeviHalfModulus_refinedBlockScalar`: so is the positive half
  modulus, whose kernel is that of the modulus (`refinedLeviHalfModulus_ker`).

The last result is the modulus cancellation used in the final bound. The
half modulus that normalizes induction is trivial on the block scalars of the
ambient `C`. Hence no extra character appears when an exponent of the
induced piece is transported to the inducing representation.

## Provenance and scope

The central-character argument is the one in Waldspurger 2003, III.2.3
(registered `waldspurger-2003-plancherel`, printed pp.266–267): exponents of a
Jacquet module of an induced representation are read off the graded pieces
of the geometric lemma. These statements are internal helpers. None of them
asserts a geometric filtration or a chamber inequality.
