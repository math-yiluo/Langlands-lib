# Actual complementary-product endpoint adapters

This module proves
`Langlands.Classification.ComplementaryEndpointRegularity.{uF, uV} F T`
with independent field and representation-carrier universes. Its adapters
serve the endpoint clause of
`Langlands.Classification.ComplementarySeriesUnitarity`, the exact statement
of Tadic (1986), Proposition 2.9, printed p.350. They concern the actual
normalized two-block product already defined by `complementaryProduct`.
The endpoint unitarity conclusion remains a separate obligation.

`complementaryProduct_admissible` proves admissibility for every real parameter
from admissibility of the input block. The proof twists each block by its actual
determinant-power character, takes the external tensor product, and applies
published normalized-induction admissibility.

`complementaryProduct_finiteLength` proves finite group-algebra composition
length for every parameter when the input block is irreducible. Twisting
preserves irreducibility, so the published theorem on normalized products of
irreducible factors applies even when the induced representation is reducible.

`continuous_complementaryProduct_distribution` proves continuity of the actual
finite-rank distribution character evaluated at each Schwartz--Bruhat test
function, for any locally finite left invariant Borel measure. It assumes
admissibility of the input block. The proof writes the inducing representation
as a real-power twist of one fixed normalized Levi inflation. The exponent
modulus is trivial on compact subgroups, since each continuous positive
determinant-norm character is trivial there. The published compact-quotient
trace theorem expresses the integrated trace as a finite sum of character
evaluations. Each evaluation is a continuous real power of a fixed positive
number. The induction is identified with the actual complementary product,
so the result concerns its distribution, independently of admissibility proof
choices.

`complementaryEndpointRegularity` packages these facts into the focused
`ComplementaryEndpointRegularity` target. Proof irrelevance identifies the
admissibility witnesses in the continuity clause.

These are derived adapters of published Library constructions, rather than a
new claim that the literature supplies extra hypotheses. The character
continuity is the specific instance needed for the role played by Tadic's
Lemma 2.8 and Theorem 2.7 in Proposition 2.9. The theorem asserting unitarity of
all irreducible constituents of a finite-length character limit is a separate
prerequisite; it is not proved here.
