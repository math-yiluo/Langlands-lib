# Local reduction of the cuspidal sigma-lift conductor formula

`CuspidalSigmaLiftConductorFromLocalEpsilonStatement` says that
`CuspidalSigmaLiftLocalEpsilonDataStatement` implies the exact Library
`CuspidalSigmaLiftConductorStatement`. Both propositions have independent
universes `u`, `v`, `uV`, and `uW`. The local data use the same field,
representation, and sigma-lift hypotheses as the target.

## Local data

- `TraceEpsilonCharacterCondition` relates `ψ_E` to `ψ_F` by the trace
  and requires additive conductors zero and `d`, respectively.
- `IsStandardEpsilonConductor` certifies a finite newvector conductor
  `a` for a representation of rank `m` and a pair factor with exponent
  `a + m * n(ψ)`. The factor is the Library's
  `AllField.RankinSelberg.IsPadicPairEpsilonFactor` against
  `RankinSelberg.rankOneCharacter 1`. The formula is required for every
  determinant twist indexed by `X` and for every orbit block. The same
  natural number `a₁` is required to satisfy
  `Conductor.IsNewvectorConductor` for `Π₁` and to be the conductor in
  each orbit block certificate.
- `OrbitProductEpsilonMultiplicativity` certifies the pair factor of
  `Π` against the trivial character and identifies its monomial
  function with the product of those of the orbit blocks.
- `EpsilonMonomialProductComparison` identifies the product of the
  twist factors over `F` with the factor of `Π` over `E`, up to a
  constant complex unit. All products and the comparison use the
  residue cardinalities of the actual local fields.

## Lean proof

`EpsilonMonomialProductComparison.sum_eq` multiplies the unit coefficients
and adds the integer exponents. Evaluating the comparison at zero identifies
the combined coefficients. Evaluating at one cancels them and leaves an
equality of powers of the residue cardinalities. Since `q_F > 1` and
`q_E = q_F ^ f`, injectivity of integer powers of `q_F` gives
`∑ e_F = f * e_E`.

The proof also applies the same lemma with `f = 1` to the multiplicativity
over `E`. Every block has exponent `a₁ + (k₁ + 1) * d`, so the exponent
of `Π` is `s * a₁ + (k + 1) * d` by the rank equality. Over `F` the
exponents are the twist conductors because `n(ψ_F) = 0`. The proof first
obtains an equality in `ℕ`. Each newvector certificate then identifies
the corresponding `Conductor.firstFixedLevel` with a finite value in
`WithTop ℕ`, which gives the target.

This internal implication formalizes the exponent comparison in
[CuspidalSigmaLiftConductorStatement.md](CuspidalSigmaLiftConductorStatement.md).
The source for the epsilon identity and product argument is Arthur and
Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the
Trace Formula* (1989), Chapter 1, Proposition 6.9(ii), printed pp. 60–61
and 69–70 (PDF pp. 74–75 and 83–84), literature ID
`arthur-clozel-1989-base-change`. The local data above are the premises
of this implication.
