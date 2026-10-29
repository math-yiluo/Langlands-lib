# Necessary whole-chamber bounds for square-integrable product Levis

Author: Worker 19.

This module proves the already published
`Langlands.GLProductLeviSquareIntegrableExponentNecessityStatement.{uF,uV}`
as `Langlands.glProductLeviSquareIntegrableExponentNecessity`.
It is an internal derivation from independently published Library proofs.

For one arbitrary supplied Borel Haar measure on the actual quotient of
`B.Levi F.Carrier` by its full center, assume
`IsSquareIntegrableModCenter σ μ`. The representation is arbitrary; no
irreducibility, nonzero carrier, finite length, finite dimensionality, or global
finite spectrum is required. The field and representation carrier retain
independent universes. Every refinement and every open-kernel generalized
eigencharacter of its actual normalized refined Jacquet action are included.
The action is pulled back through the published `flattenedLeviEquiv` and
`blockScalarLevi`, with the original inverse half-modulus normalization and
the uniform common-power occurrence predicate unchanged.

For such a character `ψ`, `T.exists_isRealPartOf` constructs scalar real-part
coordinates `x` using its open kernel. The independently published
`Exponents.RefinedUpperSquareIntegrableCone.isPositiveRootCone` places the
coordinates in the strict positive root cone separately inside each original
block. That theorem supplies each block's own zero sum, including singleton
refinements, and every strictly positive proper prefix.

The proof uses the published pairing characterizations of the open and closed
cones. A tuple whose absolute values are monotone inside each original block
has a monotone integer `logAbs` vector in that block. Its pairing with the
block's real-part coordinates is therefore nonpositive. If some block has
nonconstant absolute values, `logAbs_eq_logAbs_iff` makes its integer vector
nonconstant, and that block's pairing is strictly negative. The finite sum of
the block pairings is thus nonpositive, and is strictly negative under the
stated nonconstancy condition.

`sum_centreHMap_blocks` identifies this sum with the flattened scalar pairing.
The real-part identity gives `‖ψ(a)‖ = q ^ pairing`, where
`q = T.residueCardinality > 1`. The two pairing inequalities give exactly the
weak bound `‖ψ(a)‖ ≤ 1` on the entire blockwise chamber and the strict bound
`‖ψ(a)‖ < 1` when at least one block has nonconstant absolute values.
There are no fine-block size factors in these scalar coordinates.

The analytic strict-prefix and independent central-direction arguments are
reused from the published upper-cone helper, rather than reproved here. This
module proves only the whole-chamber necessity statement. The full strict
`GL_n` equivalence and the single-block normalized Jacquet comparison remain
separate obligations.

## Provenance and independence

The immediate mathematical inputs are the proved Library declarations
`T.exists_isRealPartOf`, `Exponents.RefinedUpperSquareIntegrableCone.isPositiveRootCone`,
`Exponents.isPositiveRootCone_iff_pairing`,
`Exponents.isClosedPositiveRootCone_iff_pairing`, and
`ProductLeviNecessity.sum_centreHMap_blocks`.
The upper-cone helper was independently reviewed and published with
`RefinedOppositeSquareIntegrableConeProof`; this proof imports the upper helper
directly and does not import the opposite-cone proof or its wrapper.
The source motivation for the already published target is Casselman's strict
exponent criterion, as documented in the unchanged target Markdown. The route
implemented here is a Library derivation through real parts and finite sums.

The transitive project import closure was audited against Library commit
`4e6ed28ccc687ea7e0123318bc2516e1f4b79d11`: 375 project modules including
this new entry. Every imported Lean/Markdown pair matches that published base.
No excluded segment analytic classification, multisegment head exhaustion,
ordered head existence or quotient coverage, tempered block uniqueness,
square-integrable Langlands classification or exhaustion, regular exhaustion,
weakly critical support, equal-exponent grouping, or downstream support proof
occurs in the closure. The only related textual occurrences are the unproved
`GLTemperedUnitarityStatement` and
`GLTemperedDiscreteSeriesSupportStatement` definitions and their aggregate
references; no proof or conclusion of either is used. In particular, the
strict GL criterion is not an input.

Relative to the earlier audited lower analytic closure, the new modules are
the present proof, its necessity statement, the imported tempered necessity
statement, and the independently published upper-cone helper. Two lower
modules have since acquired elementary shared lemmas: the scalar norm of a
determinant-power character in `SupercuspidalTwist`, and local constancy of a
continuous complex character in `ContinuousCharacterProof`. Their actual
changes add no excluded proof dependency. This derivation therefore uses
the lower coefficient, test-tuple and root-cone results without a downstream
classification or support theorem.
