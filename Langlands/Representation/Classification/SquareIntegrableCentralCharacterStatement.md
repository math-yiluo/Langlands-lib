# Elementary central-character reductions for square-integrability

Worker 19 states `Langlands.GLSquareIntegrableCentralCharacterStatement`.
This is a proposition definition, not a proof of the reductions or of the strict
Jacquet-exponent criterion.

The statement quantifies a prime `p`, a finite p-adic field `F` with supplied
compatible topology `T`, a positive rank `n`, and a nonzero complex module `V`.
The field and carrier universes `uF` and `uV` are independent. The representation
`ρ` is admissible, and scalar matrices act through the supplied homomorphism
`ω : F.Carrierˣ →* ℂˣ`. There is no irreducibility, finite-length or
finite-dimensionality hypothesis.

Under those hypotheses the four assertions are:

1. The kernel of `ω` is open for the topology induced by `T`.
2. A `UnitaryCentralCharacter ρ` on the actual group centre exists if and only
   if `‖ω(a)‖ = 1` for every field unit `a`.
3. The actual analytic predicate `T.IsSquareIntegrable ρ` implies this
   unitarity of the supplied scalar character.
4. For every fixed datum `c : UnitaryCentralCharacter ρ`,
   `T.IsSquareIntegrable ρ` is equivalent to membership of
   `c.coefficientNorm ℓ v` in `L²(μ)` for every Borel Haar measure `μ` on
   `GL_n(F)/Z`, every smooth-dual functional `ℓ`, and every vector `v`.

Clause 4 retains quantification over all Haar measures on the central quotient
with its Borel measurable structure. It does not assert that integrability for
one Haar measure implies integrability for another. It only removes dependence
on the chosen central-character witness. None of the four clauses asserts an
integrability estimate, a spectral decomposition or a Jacquet-exponent bound.

## Internal provenance and proof obligations

This is an internal auxiliary interface extracted from the definitions in
`Langlands.Representation.Classification.Tempered` and
`Langlands.Representation.MatrixCoefficient.ModuloCenter`. It is not a
translation of a separate literature theorem.

Smoothness provides an open subgroup fixing a chosen nonzero vector; continuity
of the scalar embedding and cancellation of scalar multiplication give clause 1.
At positive rank the actual centre consists exactly of scalar matrices, and the
scalar embedding is injective. Transport of a unitary `ω` across that group
isomorphism supplies the centre character; its open kernel is obtained from
smoothness again. Conversely, comparison of the two scalar actions on a nonzero
vector determines `ω`. The open-kernel argument and this centre construction
are adapted from Worker 349's private helper proofs in
`TemperedExponentEdgeProof`; Worker 349 is credited as a coauthor.

Clause 3 additionally uses the published existence of a Haar measure on the
actual central quotient, so its analytic hypothesis is not used vacuously.
Clause 4 uses `UnitaryCentralCharacter.coefficientNorm_eq`, which identifies the
descended coefficient norms for different witnesses. These are intended proof
routes and remain obligations of the proof successor.

The sole direct import is `Langlands.Representation.Classification.Tempered`.
No exponent criterion, segment classification, multisegment exhaustion,
Langlands quotient coverage or tempered block uniqueness result is a premise.
This auxiliary statement leaves the unchanged strict criterion
`GLSquareIntegrableExponentCriterionStatement` unproved.
