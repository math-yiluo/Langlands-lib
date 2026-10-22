# Rank-one newvectors from smoothness

This module constructs a finite first fixed level and an actual nonzero
vector at that level for every nonzero smooth representation of
`Matrix.GeneralLinearGroup (Fin 1) F`. The field is a nonarchimedean
local field with its given valuative topology. The coefficient ring is
any commutative ring, and the coefficient, field and module universes
are independent. There is no admissibility or finite-dimensionality
hypothesis and no assumed existence of a finite fixed level.

The construction uses the actual level subgroups from the sibling
congruence module. Over the integer ring, the intersection of their
last-row congruence conditions is the identity: in rank one the condition
is `g(0,0) - 1 ∈ m^a`, and Krull intersection gives
`⋂ a, m^a = {0}`. The integer ring is a discrete valuation ring and
therefore Noetherian. Injectivity of the integral matrix inclusion
transports this identity to the field group.

Each level subgroup is compact and closed, and the family decreases.
The compactness lemma for decreasing closed sets shows that every
neighborhood of their intersection contains a member of the family.
Thus these rank-one subgroups are cofinal in the neighborhoods of one.
Given a nonzero vector, smoothness supplies an open fixing subgroup;
a level subgroup contained in it fixes that same vector. This proves
`HasNewvectorLevel`, which the existing least-level and nonzero-vector
constructors then consume. `rankOneConductor` and `rankOneNewvector`
have this existence proof implemented internally.

This is a derived topological construction accompanying the rank-one
specialization of JPSS's congruence family, not a proof of the
higher-rank generic newvector theorem. The intersection of the
higher-rank last-row subgroups is not trivial, so this argument is
deliberately restricted to rank one. No equality with an epsilon
exponent, dimension-one statement or essential Whittaker normalization
is claimed.

## Provenance and dependencies

H. Jacquet, I. I. Piatetski-Shapiro and J. Shalika, *Conducteur des
representations du groupe lineaire*, Math. Ann. 256 (1981), 199–214,
Section 5.1, page 211 (PDF page 13), supplies the congruence family
and the least nonzero fixed-level interpretation. The proof here is a
derived rank-one argument using compactness and Krull intersection,
rather than the source's higher-rank representation-theoretic argument.

- Literature ID: `jpss-1981-conductor`.
- SHA256: `986b06d6c16221fd55f04480604a1b17bf11004a704ab16b78acdd131ae6d49d`.
- Retained PDF:
  `C:/Central-Library/Jacquet-Piatetski-Shapiro-Shalika--Conducteur des representations du groupe lineaire--1981.pdf`.

Project dependencies are the published modules
`Langlands.Representation.Conductor.Congruence`,
`Langlands.Representation.Conductor.Definitions`, and their shared
`Langlands.Representation.Smooth.Definitions` dependency. The conductor
pairs are present in Library commit
`1804f2a6d98d21c2bbfa3c73ccf807df74c484bb`; their published bytes were
verified against the inputs used here. The imports refer to the
published Lean declarations.

Pinned Mathlib supplies `Ideal.iInf_pow_eq_bot_of_isLocalRing`,
the local-field integer-ring instances and
`exists_subset_nhds_of_isCompact'`. Environment:
`2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1, Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Worker 43 authored this module. Independent review and publication
remain necessary.
