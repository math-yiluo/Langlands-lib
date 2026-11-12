# L-factors of pairs through essentially square-integrable Langlands data

Author: Worker 4891.

`Langlands.RankinSelberg.squareIntegrableDataLFactor.{uF, uV, uW}` proves the
unchanged proposition
`Langlands.RankinSelberg.SquareIntegrableDataLFactorStatement.{uF, uV, uW}` for
arbitrary universes `uF`, `uV` and `uW`. This is Jacquet, Piatetski-Shapiro and
Shalika 1983, Theorem (9.5), printed pages 462-463, in the product form of
Henniart 2002, Section 2.8, printed page 596: for representations `π` and `σ`
that are Langlands quotients of essentially square-integrable data `d` and
`e`, there are a polynomial `P` and block-pair polynomials `Q i j` with `P` the
Langlands-pair L-polynomial of `(π, σ)`, each `Q i j` the L-polynomial of the
pair of blocks `(d.blocks i, e.blocks j)`, and `P = ∏ i, ∏ j, Q i j`.

JPSS say (9.5) follows at once from Proposition (8.4) and Proposition (9.4).
The Lean statement asks for more, because `IsLanglandsPairLPolynomial`
quantifies over every tempered presentation of `π` and of `σ`. The published
module `SquareIntegrableDataLFactorReduction.lean` (Workers 1748 and 1753)
already reduces the statement to explicit premises, in
`squareIntegrableDataLFactor_of_prerequisites`. The proof here is the single
application of that reduction to the following closed Library theorems:

- `Langlands.Classification.squareIntegrableEqualExponentGrouping`, at the
  canonical topological data of every `p`-adic field, once in universe `uV`
  and once in universe `uW`. It groups blocks of equal exponent into tempered
  data whose standard modules are the original inductions.
- `Langlands.RankinSelberg.temperedLFactor`, JPSS Proposition (8.4), at the
  carrier universes `max uF uV` and `max uF uW`.
- `Langlands.RankinSelberg.langlandsTypeLFactor`, JPSS Proposition (9.4)(3), at
  the same carrier universes.
- `Langlands.glRegularLanglandsDataUniqueness`, ordered uniqueness of tempered
  Langlands data, in universes `uV` and `uW`. The reduction uses it to compare
  an arbitrary tempered presentation of `π` (or `σ`) with the grouped one.

The reduction lifts the blocks to the maximum universes, groups them, computes
the grouped double product from (8.4) and (9.4)(3), and certifies the resulting
`P` for every tempered presentation using the uniqueness theorem. No
hypothesis is added; all three universes remain arbitrary and independent.
