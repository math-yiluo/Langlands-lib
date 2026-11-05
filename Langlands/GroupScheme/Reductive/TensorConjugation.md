# Conjugation maps from actual tensor-dual intertwiners

This internal construction takes an actual matrix representation `σ` of an
affine group scheme over a field of arbitrary universe `u`. Given an actual
intertwiner `C` from a representation `ρ` to `σ.tensor σ.dual`, it constructs a
`ConjugationLinearMap ρ σ`. The intertwiner is supplied; this module does not
assert its existence or the irreducibility of `σ`.

The coordinates of the tensor use ordered pairs `(i,j)`, with the original
factor first and the dual factor second. `MatrixLinear.tensorCoefficients`
reshapes the output coordinate `(i,j)` of `C` into matrix entry `i,j`.
Its evaluation after every scalar extension is the corresponding entry of
`C.map f *ᵥ x`. In particular, it preserves a nonzero base-field image.

`tensor_dual_pointMatrix_mulVec` proves the exact action identity on every
relative scheme test, without an affineness or reducedness condition on that
test. The tensor action multiplies coordinates by
`σ(g) i a * σ(g)⁻¹ b j`, since the second factor is the inverse transpose.
Expansion and interchange of the two finite sums give matrix conjugation.

`ConjugationLinearMap.ofTensorIntertwiner` uses `Intertwines.points` to turn
the given affine-test intertwiner into an identity on all scheme tests, then
uses the tensor-dual action identity. The resulting coefficient maps satisfy
the unchanged all-test conjugation-equivariance definition. The final two
lemmas state its base-field evaluation and the equivalence of nonvanishing
before and after reshaping.

The provenance is internal: finite sums, the existing actual tensor and dual
group-scheme representations, and the published all-test intertwiner bridge.
No Steinberg module, self-duality isomorphism, coordinate-ring exhaustion,
geometric reductivity or characteristic assumption is constructed here. This
adapter alone does not prove
`SimplyConnectedPositiveCharConjugationMapStatement`.
