# Haar normalization invariance of temperedness modulo the center

Author: Worker 573.

`Langlands.temperedModCenterHaarInvariant` proves the closed proposition
`Langlands.TemperedModCenterHaarInvariantStatement` with independent group
and representation-carrier universes. The helper
`Langlands.isTemperedModCenter_iff_haar` gives the equivalence for a supplied
representation and two Haar measures on the same Borel measurable space of
its actual central quotient. Local compactness and second countability of
that quotient remain explicit hypotheses.

For each direction, the implemented proof unpacks analytic temperedness as
admissibility, a unitary central character, and membership of all absolute
smooth-dual coefficients in `L^(2 + ε)` for every positive real `ε`.
It retains admissibility and exactly the same central-character witness.
For every functional, vector and positive `ε`, it applies the published
`Langlands.haarMemLpInvariant` to the real function
`c.coefficientNorm ℓ v` and exponent `ENNReal.ofReal (2 + ε)`.
The forward or reverse implication of that equivalence transfers the
required `MemLp` fact. The closing theorem introduces all parameters and
applies the helper.

This proof is an internal deduction from the published analytic definition
and generic Haar `MemLp` invariance. The imported Haar theorem uses Haar
uniqueness and finite measure scaling; this proof requires no new choice or
comparison of central characters. It applies also to zero carriers, and
assumes neither irreducibility nor a positive form.

This result establishes invariance only within one supplied Borel
realization. Actual GL or product-Levi quotient topology and adapters between
Borel realizations remain separate results. No induction, exponent criterion,
tensor comparison or classification theorem is used.
