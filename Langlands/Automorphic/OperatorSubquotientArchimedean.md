# Compact covariance and center finiteness on actual automorphic quotients

This internal construction works over every number field `F : Type uF` and
natural rank `n`, with complex coefficients. Its inputs are actual
`OperatorRealization` numerators and `OperatorSubquotient` presentations. The
quotient carrier remains `Q.upper.Space ⧸ Q.lower.toSubmodule`, with the
previously constructed induced operator action and canonical projection.
No extra covariance or finiteness hypotheses are added to these inputs.

For a realization `S`, `centerAction` restricts its genuine complex enveloping
algebra action along `ArchimedeanGL.centerInclusion`. `centerRepresentation`
is the multiplicative representation of that same algebra action.
`centerAmbientInclusion` takes the actual realized vector into its
finite-smooth rational-invariant function, using `S.formInclusion` and
`automorphicFiniteSmoothInclusion`. It intertwines the center actions because
all are restrictions of the same differential operators, and it is injective
as a composite of the two published faithful inclusions.

`centerRepresentation_isFiniteVector_iff` identifies finite dimensionality of
the entire center orbit span of a realized vector with the existing
`IsCenterFinite` predicate on its actual smooth function. The proof reflects
orbit finiteness through `centerAmbientInclusion` and uses the published
faithful slice-family comparison in `DifferentialCenterFinite`. This is one
finite span for the complete family of slices, rather than a separate finite
span chosen at each slice. `centerRepresentation_isFiniteVector` obtains this
condition from membership of the actual image in the existing automorphic
form space.

For a quotient `Q`, `compactProjection` equips its canonical projection with
equivariance for the entire `standardInfiniteCompact F n` action.
`map_compactOrbitSpan` identifies the quotient compact orbit span exactly
with the linear image of the numerator compact orbit span. Every quotient
vector has a numerator representative, so the published compact finiteness
of that representative descends through this intertwiner. This proves
`compactRepresentation_isFiniteVector` for every quotient vector.

`finiteRepresentation_compactRepresentation` proves that finite adelic
translation commutes with compact translation on the quotient.
`compactRepresentation_envelopingAction` proves its actual adjoint covariance:
if `R(k)` is compact translation and `D(a)` is the genuine enveloping action,
then `R(k) D(a) f = D(envelopingConjugation F n k.val a) R(k) f`.
Both proofs use quotient induction and apply the canonical projection to the
published numerator identity. In particular, covariance is derived from the
actual action, rather than supplied as another structure field.

`compactLinearEquiv k` is the invertible complex-linear map supplied by the
quotient group representation, with inverse translation by `k⁻¹`, as the two
application formulas record. Finite/compact commutation makes this same map
`compactFiniteEquivalence k`, a genuine equivalence of the finite adelic
quotient representation with itself.

The quotient `centerAction` restricts its existing algebra action along the
same actual center inclusion, and `centerRepresentation` retains its
multiplicative representation. `centerProjection` is the canonical quotient
projection with center covariance. `centerAction_projection` records the
representative formula. `map_centerOrbitSpan` proves that the entire center
orbit span in the quotient is exactly the projected numerator orbit span.
The realization finiteness theorem and representative lifting therefore give
`centerRepresentation_isFiniteVector` for every quotient vector.

`finiteRepresentation_centerAction` specializes the previously proved
finite/enveloping commutation to the actual center inclusion.
`envelopingAction_centerAction` proves that every differential commutes with
every central differential on the quotient. Its proof carries the central
multiplication identity through the genuine quotient algebra homomorphism
and applies the resulting endomorphisms to the vector.

Provenance is internal: the published `OperatorSubquotient`,
`OperatorCompactCompatibility`, `DifferentialCenterFinite`, `Forms`,
`OperatorRealization`, `ArchimedeanLieAlgebra`, and `FiniteVectors`
constructions, together with Mathlib's conversion from invertible
endomorphisms to linear equivalences. No new identification with original
literature is asserted. Every action used here is the restriction or quotient
of the published actual function operators.

Finiteness means finite dimensionality over the complex numbers of each
specified orbit span; it does not make the entire quotient finite dimensional.
The construction adds no topology or analytic differentiability assertion on
the quotient, no identification of the compact derivative with its Lie action,
and no quotient evaluation as a function. It supplies neither admissibility,
irreducibility, a local tensor factor, nor an automorphic or spectral existence
theorem. Such assertions remain separate obligations.
