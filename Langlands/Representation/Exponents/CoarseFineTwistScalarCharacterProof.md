# Coarse scalar character of a nested fine twist: proof

Authors: Worker 526, using Worker 359's effective-parameter and fibre-sum
calculation. Worker 438 adapted the shared proof for submission and checked
its build, declaration and published imports. Imported published results
retain their own provenance.

`Langlands.Exponents.coarseFineTwistScalarCharacter` proves exactly
`Langlands.Exponents.CoarseFineTwistScalarCharacterStatement.{uF,uV}`.
The field and representation carrier universes remain independent. The
published statement and all its imports are used unchanged.

This is an internal algebraic deduction from the public
`unitaryFineTwistScalarCharacter`, `positiveRootBlockSums`, the flattening
coordinate lemmas in `Classification.MaximalConeLifting`, and
`PadicField.TopologicalData.isRealPartOf_coarsen`. It is not a theorem
transcribed from the literature.

The proof first transports the fine representation and fine vector along
the supplied literal equality of flattened shapes. A private
`transport_properties` lemma transports any proposition on a shape and a
representation of that shape's actual Levi. It is applied to the conjunction
of irreducibility, admissibility and unitarizability, so the three properties
refer to the same actual transported representation `ωB`.

For each coarse real vector `t`, set
`v' k = vB k - t (B.flattenOuter S k)`. The zero-coarse fine twist with
parameter `v'` is the requested fine twist with parameters `vB,t`, since
`-(vB k - t i) = -vB k + t i`. The proof establishes equality of these
actual representations by unfolding `fineTwist` and rewriting their
determinant exponents. The public unitary fine scalar-character theorem
applied to `ωB,v'` therefore supplies the scalar action on the required
representation, with a fine tuple character `χf` of open kernel.

The proof defines the repeated-coordinate homomorphism from coarse tuples
to fine tuples by `a ↦ a ∘ B.flattenOuter S`, and takes
`χ = χf.comp repeatCoords`. Each coordinate of this map is a product
projection, hence continuous; the inverse image of the open kernel of
`χf` is the open kernel of `χ`. Evaluating the fine scalar-action
identity at that repeated tuple is exactly the scalar-action identity
in the target, including its specified forward `flattenedLeviEquiv`.

To compute the real part, the third clause of `positiveRootBlockSums`
gives a zero coordinate sum in each coarse block after the same equality
transport. Reindexing by the actual `(S i).indexEquiv` and then
`Fintype.sum_sigma` separates its fine blocks and their coordinates.
`B.index_index_eq_flatten` and `blockIndex_index` identify each coordinate's
fine block. Summing the repeated value over that fine block gives

```text
∑ k : Fin (S i).length,
  ((S i).size k : ℝ) * vB (B.flattenBlockEquiv S ⟨i,k⟩) = 0.
```

The public `isRealPartOf_coarsen` sums the fine real coordinates over the
fibres of `flattenOuter`. The public `sum_filter_flattenOuter` rewrites
each fibre as the fine blocks of `S i`. The preceding zero sum cancels
the contribution of `vB`, and `(S i).sum_eq` shows that the remaining
sizes sum to `B.size i`. Thus the coarse real part is precisely
`fun i => (B.size i : ℝ) * t i` in the existing residue-normalized
absolute-value convention. Finite sums also cover empty shapes, so no
positive-rank or block-count premise is introduced. The same argument covers
one-block shapes and refinements with an empty adjacent-root index: the
published block-sum theorem already includes these cases.

The proof uses exactly the stated hypotheses and arbitrary `t`. It
constructs the tuple character and its scalar action; it does not establish
a full-center character, a generalized-block decomposition or exactness,
Jacquet compatibility, a geometric identity layer, exponent exclusion,
Hom factorization, a dimension comparison or a classification result.
