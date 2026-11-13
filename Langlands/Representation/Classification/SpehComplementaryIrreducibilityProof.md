# Irreducibility of complementary products of Speh representations

`Langlands.Classification.spehComplementaryIrreducibility` proves the exact
proposition `SpehComplementaryIrreducibility` with independent field and
representation universes. For every supplied Speh representation `S = u(δ,k)`
and every real parameter `α` with `-1/2 < α < 1/2` and `α ≠ 0`, its actual
normalized product `ν^α S × ν^(-α) S` is irreducible.

The proof applies `spehIntegralLineSupport` to the given `IsSpeh` relation.
This supplies an actual supercuspidal-support multiset `s` of `S` and a
cuspidal datum `ρ` such that every member of `s` is `ρ.twist m` for an integer
`m`. It then applies `integralLineComplementaryIrreducibilityReduction`,
discharging its unlinked-product premise with the unconditional theorem
`unlinkedSocleProductIrreducibility`.

The positive rank required by the reduction is
`d.degree = d.length * d.rank`; positivity follows from the two positive
Speh parameters. The reduction concludes irreducibility of the uniform
two-block induction with exponents `α` and `-α`. That induction is
definitionally `d.complementaryInduced S α`, so no rank transport is needed.
The separate discrete-series premise in the fixed target is already included
in the given `IsSpeh` relation.

This is a derived composition of the integral-line support construction, the
integral-line separation reduction, and the unlinked-socle product theorem.
The separation reduction uses that `2α` is a nonzero real strictly between
`-1` and `1`, hence not an integer; the two twisted supports therefore lie on
different integral cuspidal lines and have no linked cross-segments. The
final theorem introduces no unitarizability, Bernstein, or unproved
classification hypothesis.
