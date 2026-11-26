# Conjugation of simple characters with their additive trace factor

Bushnell–Kutzko, *The admissible dual of GL(N) via compact open
subgroups* (1993), source ID `bushnell-kutzko-1993-admissible-dual-gln`,
SHA-256 `811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`,
(3.3.5) and (3.3.9), printed pp. 107–108 (PDF pp. 119–120).

`SimpleCharacterCovarianceStatement` isolates the second identity of (3.3.9)
for the successor simple character. In the notation of (3.3.9), the
element of the stratum in this statement is the successor `γ`, and the
shallower index `t` is the preceding critical depth `r`. The index `t`
is supplied directly. The indices `m` and `t` are below the
stratum level and the critical depth of the successor, and `⌊t/2⌋≤m`.
The second identity's computation in (3.3.5) uses these inequalities in
the commutator estimate. This form also allows equivalent-stratum
comparisons at a depth specified independently of a defining sequence.

The double coset uses `simpleCharacterIntertwiningFactor` at `t`, including
its scalar convention. For each unit `g` in that double coset, the
conjugation ratio is the additive function with coefficient `g⁻¹γg − γ`
on the whole intersection of the two domains. The first identity in
(3.3.9) involves a preceding character related by a twist. Its trace
factor comes from the same ratio by conjugating the twisting function.

`elementCharacter_conj` proves this elementary transformation by cycling
products inside the trace. `elementCharacter_conjugationDifference_mul`
expands the coefficient difference for two successive conjugations and
uses additivity of the trace character. `characterConjugationRatio.mul_of_overlap`
uses this identity to compose the formulas when the intermediate conjugate
belongs to the domain. `characterConjugationRatio.of_twist` adds the twist
coefficient to the conjugation difference for a character obtained by
pointwise multiplication by an element character on the same domain.
