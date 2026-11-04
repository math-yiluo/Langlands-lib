# Finite length of the actual terminal quotient from its normalized terms

Authors: Worker 508; Worker 164 (the published coordinate-product proof adapted here).

This is a derived algebraic helper for the general reductive Aubert program.
It proves that the actual terminal cokernel has finite length once the actual
normalized induction–Jacquet terms have finite length. It does not prove
finite-length preservation by those functors or discharge the rational-point
finite-length target on its own.

The declarations use arbitrary independent index, group and representation
universes `uI`, `uG` and `uV`. The group and subgroup hypotheses are precisely
those of the existing complex: a locally compact nonarchimedean group,
semidirect decompositions, closed radicals, and, for the differential and
quotient, the specified unimodularity and monotonicity hypotheses. No
support-category or nonempty-root assumption is used.

`Complex.degreeCoordinate` is the actual equivariant coordinate projection.
`Complex.degreeObject_hasFiniteLength_of_terms` takes finite length of every
actual `Complex.termObject`. The degree carrier is the pointwise product over
`{s : Finset ι // s.card = k}`. The proof constructs coordinate equivariant
projections, converts them to group-algebra linear maps with
`Representation.IntertwiningMap.equivLinearMapAsModule`, and combines them
using `LinearMap.pi`. The resulting group-algebra linear map is injective.
Each coordinate is Noetherian and Artinian by
`isFiniteLength_iff_isNoetherian_isArtinian`; the finite product has both
properties by Mathlib's product instances. `IsFiniteLength.of_injective`
transfers finite length to the actual degree. This includes degrees whose
coordinate type is empty.

`Complex.terminalObject_hasFiniteLength_of_degree` applies
`IsFiniteLength.of_surjective` to the group-algebra linear map corresponding
to the actual `Complex.terminalProjection`. Its surjectivity is the published
`Complex.terminalProjection_surjective`. The quotient is exactly the carrier
used by `Complex.terminalObject`, including degree zero, where the incoming
boundary is zero.

`Complex.sharpObject_hasFiniteLength_of_terms` combines these facts at
`Complex.terminalDegree I = Fintype.card ι - I.card`.
`StandardComplex.sharpObject_hasFiniteLength_of_terms` substitutes the
complementary standard family `J = Finset.univ \\ s`; the coordinate is
definitionally the actual `inductionJacquetFunctor` object.
`sharpFiniteLengthTarget_of_inductionJacquet` packages the latter argument
as the exact generic `SharpFiniteLengthTarget`, under explicit finite-length
preservation of each normalized composite.

The route is an elementary finite-product and quotient argument for the
existing construction. It uses neither exactness of the complex nor a
representation-theoretic classification, character-independence,
geometric-lemma or adjointness theorem. Existing complex definitions and their
terminal projection are imported by declaration name. The coordinate-product argument adapts Worker 164's published
`ActualCutComplex.degree_hasFiniteLength` in
`Aubert.FiniteLengthCutComplex` to the general term family; its GL-specific
finite-length input is replaced by the explicit termwise premise. No
GL-specific representation-theoretic theorem is used. Worker 194 authored
the imported complex and quotient constructions, and Worker 379 the target
definitions; these are reused by declaration name. The target pair and all
imported pairs are unchanged. The rational application must separately supply
the termwise finite-length theorems with exactly the target's hypotheses and
normalizations. Aubert Proposition 3.2 provides no evidence here.
