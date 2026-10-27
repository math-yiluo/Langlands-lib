# Actual subspaces under smooth and normalized parabolic induction

This internal construction detects supplied invariant subspaces inside actual
smooth induction. It uses the existing value subrepresentation, consisting of
smooth covariant functions whose values all lie in a given subspace.

`Langlands.Induction.exists_valueSubrep_eval` starts with a smooth representation
of a subgroup of a nonarchimedean, weakly locally compact group. For each vector
in an invariant subspace it constructs a smooth induced function valued in that
subspace whose value at the identity is the specified vector. The restricted
representation is smooth because its inclusion is injective. A compact local
section of that restricted representation, with the whole quotient as its open
neighborhood, supplies the function. Postcomposition with the inclusion returns
it to the original induced space. The prescribed-value theorem gives evaluation
at the identity, and every value belongs to the supplied subspace by construction.
No closedness assumption on the subgroup is needed.

`Langlands.Induction.valueSubrep_le_iff` uses these functions to reflect inclusion
between actual invariant subspaces. Apply an assumed inclusion to the function
associated to a vector and evaluate at the identity. Preservation of inclusion
is the existing pointwise monotonicity. The coefficient field, group and carrier
universes are independent. Smoothness of the inducing representation is explicit.

`Langlands.Parabolic.normalizedInducedSubrepresentation T B σ S` specializes the
value construction to actual normalized upper block-parabolic induction for a
supplied p-adic field and compatible topology. Its ambient representation is
exactly `T.normalizedParabolicInduced B σ`. The construction uses the same
underlying Levi subspace `S`, after inflation and the positive half-modulus twist.
It preserves bottom and top without smoothness assumptions.

`normalizedInducedSubrepresentation_le_iff` proves reflection and preservation
of inclusion under smoothness of the Levi representation. The same invariant
subspace is invariant under inflation and scalar twisting. Inflation through the
continuous Levi projection and twisting by a character with open kernel preserve
smoothness. The actual general linear group has the required nonarchimedean and
local compactness properties, so the generic reflection theorem applies.

The two final theorems preserve nonzero and proper subspaces, respectively, by
inclusion reflection and the endpoint identities. There is no restriction on the
block shape or ambient rank. Field and carrier universes remain independent.

Provenance is internal assembly of the published compact local section API,
smoothness transfer along injections, the actual value subrepresentation in
`Parabolic.InductionFactorMatchingProof`, and the published p-adic normalized
induction and general linear topology constructions. This proves no segment,
multisegment, irreducibility or classification assertion.
