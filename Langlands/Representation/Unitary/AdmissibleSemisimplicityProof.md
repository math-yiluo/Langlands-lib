# Algebraic semisimplicity of admissible unitary representations

`Langlands.admissibleUnitarySemisimplicity` proves the complete proposition
`Langlands.AdmissibleUnitarySemisimplicityStatement`, with independent group
and carrier universes.

The proof chooses the invariant positive Hermitian form provided by
unitarizability. For each subrepresentation `S`, its inclusion is an injective
intertwiner, so `isAdmissible_of_injective` makes `S` admissible and
`InvariantPositiveForm.comap` restricts the form to `S`.

The subspace `C` consists of vectors `v` with `b(v,s) = 0` for every `s` in
`S`. Conjugate linearity in the first variable proves that `C` is a complex
subspace. Form invariance and invariance of `S` under the inverse group element
prove that `C` is a subrepresentation.

For each ambient vector `v`, `b.toSmoothDual` gives the smooth functional
`b(v,-)`. Pulling it back along the inclusion through `contragredientMap`
gives a smooth functional on `S`. The published
`InvariantPositiveForm.toSmoothDual_surjective`, applied to the restricted
form, supplies `s` in `S` with `b(s,t) = b(v,t)` for every `t` in `S`.
Thus `v-s` belongs to `C`. This establishes that `S` and `C` span the whole
carrier. If a vector belongs to both, its self-pairing is zero, so positive
definiteness makes it zero. These are exactly the disjointness and
codisjointness conditions defining the required complemented lattice.

This is an internal proof using the published
[smooth-dual identification](HermitianDual.md) and
[admissibility inheritance](../Smooth/Admissibility/EmbeddingProof.md).
Compact-open cofinality is used by the smooth-dual surjectivity theorem.
No topology or completeness on the carrier, finite-length hypothesis, or
infinite-dimensional Riesz representation theorem is needed. This result
supplies the general semisimplicity step; the unitarity and analytic
preservation inputs for tempered induction remain separate obligations.
