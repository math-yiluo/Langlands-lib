# Base case and parity inputs for the one-place induction

These three unproved input statements use `IsAuxiliaryValid` and
`IsAuxiliaryValidAtParity`, the one-place hypotheses of the internal
induction. They retain every condition in those predicates. They impose
no condition on the unused primary place or primary local character.
They keep number fields in `Type 0` and allow independent local-field
and local-factor universes `uF` and `uV`.

`Proposition48AuxiliaryRankOneStatement` supplies the original four-part
`HasSolution` conclusion whenever `[E':E] = 1`. Weak induction forces
the actual automorphic rank to be one. The infinity-parity hypothesis
then has index zero, so the character has integral algebraic infinity
type. This is the Hecke-character realization base case. It includes
weak induction of the supplied character, regular algebraicity,
conjugate self-duality and the supercuspidal auxiliary component.

`Proposition48AuxiliaryParityNormalizationStatement` supplies a genuine
Hecke character `ν` of the base field and a new auxiliary local
character. `IsAuxiliaryParityNormalization` requires conjugate inversion
of `ν`, its correcting infinity parity
`(b + ([E':E] - 1)) % 2`, and `ν = 1` if the inherited and rank parities
agree. The corrected inducing character is exactly
`ξ · (ν ∘ N_{E'/E})`, using the actual idele-class norm. The corrected
problem has full one-place validity at its own rank parity. Thus the
prescribed auxiliary component and local general position must also be
constructed; they are not omitted from the conclusion.

`Proposition48AuxiliaryParityUntwistStatement` applies to every supplied
normalization and every supplied corrected solution class `c`. It
produces actual raw and corrected cuspidal realizations `S,T` of the
same rank, with `T.isoClass = c`. The imported `IsUntwistedSolution`
requires genuine multiplication of their automorphic functions by
`ν(det g)`, weak induction of the raw character for `S`, conjugate
self-duality and the auxiliary supercuspidal component. Only the
corrected realization `T` is required to be regular algebraic.
The raw realization is not silently assigned the corrected rank parity.

`Proposition48AuxiliaryPreparationStatement` is precisely the conjunction
of these three statements. Its projections can be explicit hypotheses
of subsequent reductions. It is a grouped proof target, not a theorem.
The previously stated two-place rank-one and parity interfaces are
specialized companions; they do not supply the one-place versions
because they require a second compatible, distinct place.

Source: M. Harris, *The local Langlands conjecture for GL(n) over a p-adic
field, n < p*, Invent. Math. 134 (1998), 177–210,
`harris-1998-local-langlands`. The rank-one induction start is on printed
p.202 (`math_9611226v1.tex`, lines 1588–1590). The inherited conditions
(i)–(iii) and the auxiliary supercuspidal component occur on pp.202–203
(lines 1583–1614, 1648–1666). The normalization on p.195 and half-integral
twist remark on p.191 (lines 866–875) explain the parity issue.

The one-place theorem scope, conjugate-inverse correcting base character
and actual determinant-untwisting formulation are derived formalization
choices, not verbatim claims of Harris. These are additional explicit
proof obligations. In particular neither unitary central character nor
ramified local–global compatibility is inferred by these statements.
The published Proposition 4.8 and its hypotheses are unchanged.
