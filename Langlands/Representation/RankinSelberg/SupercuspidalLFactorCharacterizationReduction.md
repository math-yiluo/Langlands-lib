# Henniart 2002, Théorème 1.6(b), from its inputs

Author: Worker 1719.
This module, in namespace
`Langlands.RankinSelberg.SupercuspidalLFactorCharacterization`, proves the
characterization of supercuspidal representations by L-factors of pairs,
`SupercuspidalLFactorCharacterizationStatement` (Henniart, *Une caractérisation
de la correspondance de Langlands locale pour GL(n)*, Bull. SMF 130 (2002),
Théorème 1.6(b), (i) ⇔ (ii), printed pages 590-591), from five hypotheses, all
of them Library statements:

- `h81 : SupercuspidalUnequalRankLFactorStatement` (JPSS 1983, (8.1)(i)):
  `L(s, π × σ) = 1` for `π` irreducible supercuspidal and `σ` of Whittaker type
  of smaller rank;
- `h94 : LanglandsTypeLFactorStatement` (JPSS 1983, (9.4)(3)): the L-polynomial
  of two standard modules of tempered Langlands data is the product of the
  L-polynomials `Q i j` of their twisted blocks;
- `hS1V`, `hS1W : Classification.SupercuspidalTemperedQuotientSingleBlockStatement`
  (in universes `uV` and `uW`): a tempered Langlands datum whose Langlands
  quotient is supercuspidal has one block;
- `hS2 : TemperedTwistSupercuspidalPoleStatement`: for an irreducible tempered
  `τ` of `GL_k(F)` and real `u`, some irreducible supercuspidal `ρ` of rank
  `≤ k`, and `< k` unless `τ` is supercuspidal, makes `L(s, ν^u τ × ρ)` have a
  pole at `s = 0`.

The L-factor of the target is `IsLanglandsPairLPolynomial`: `π` and `ρ` have
tempered Langlands data, and for all such data `d`, `e` the standard modules
have L-polynomial `P`. The helper results come from
`SupercuspidalLFactorCharacterizationSupport`.

## (i) ⇒ (ii)

`isLanglandsPairLPolynomial_one_of_isSupercuspidal`: let `π` (rank `n+1`) and
`ρ` (rank `r+1`, `r < n`) be irreducible supercuspidal. Both have Langlands data
(`exists_temperedLanglandsDatum_isLanglandsQuotient`). Given any data `d` of `π`
and `e` of `ρ`, S1 gives one block each, so the standard modules are equivalent
to `π` and `ρ` (`TemperedLanglandsDatum.nonempty_standardModule_equiv_of_length_eq_one`,
reused from `Classification/RankOneLanglandsStandardModule`). JPSS (8.1)(i)
applied to `π` and `ρ` (of Whittaker type by
`isOfWhittakerType_of_isSupercuspidal`) gives the L-polynomial `1`; the
published `isPadicSymmetricLPolynomial_of_le` turns it into the symmetric
relation and `IsPadicSymmetricLPolynomial.congr_equiv` transports it to the
standard modules.

## (ii) ⇒ (i)

Two lemmas:

- `isSupercuspidal_of_length_eq_one`: a Langlands quotient of a one-block datum
  whose block is supercuspidal is supercuspidal: it is equivalent to the
  standard module, hence to the twisted block transported along the rank cast
  (`singleBlockStandardModuleEquiv`), and supercuspidality is preserved by
  equivalence (`isSupercuspidal_of_equiv`), rank casts and twists
  (`isSupercuspidal_twist_iff`).
- `size_le_or_not_isSupercuspidal`: for a datum `d` of a non-supercuspidal `π`
  of `GL_(n+2)(F)` and a block `i`, either `size i ≤ n + 1` or `size i = n + 2`
  and block `i` is not supercuspidal. With one block, the size is `n + 2` and
  the previous lemma excludes a supercuspidal block; with at least two blocks,
  another block of positive size takes part of the total `n + 2`.

`isSupercuspidal_of_forall_isLanglandsPairLPolynomial`: let `π` be irreducible
of `GL_(n+2)(F)` with `L(s, π × ρ) = 1` for all irreducible supercuspidal `ρ` of
rank `r + 1 ≤ n + 1`, and suppose `π` is not supercuspidal. Take a datum `d`
of `π` and its first block `i` (the shape is nonempty since the sizes add up to
`n + 2`). S2 applied to the block `τ = d.blocks i` with exponent `u = d.exponent i`
gives `ρ` of rank `r + 1` and `P` with `L(s, ν^u τ × ρ) = 1 / P(q^(-s))` and
`P(1) = 0`; by `size_le_or_not_isSupercuspidal` and the rank bounds of S2,
`r ≤ n`. The hypothesis at `ρ` gives a datum `e` of `ρ`, one-block by S1, and
says the standard modules of `d` and `e` have L-polynomial `1`. By JPSS (9.4)(3)
this L-polynomial is also `∏_i ∏_j Q i j`; so `Q i j` (with `j` the only block of
`e`) divides `1`, is a constant, and equals `1` because L-polynomials have
constant term `1` (`IsPadicRankLPolynomial.coeff_zero'`). The only twisted
block of `e` is equivalent to `ρ` (`singleBlockStandardModuleEquiv` and
`TemperedLanglandsDatum.nonempty_standardModule_equiv_of_length_eq_one`), so `Q i j` is also the
L-polynomial of `(ν^u τ, ρ)` (`isPadicRankLPolynomial_comp_reindex_iff`,
`isPadicRankLPolynomial_congr_right`), and uniqueness gives `P = Q i j = 1`,
contradicting `P(1) = 0`.

## Main theorem

`supercuspidalLFactorCharacterization_of (h81) (h94) (hS1V) (hS1W) (hS2) :
SupercuspidalLFactorCharacterizationStatement.{uF, uV, uW}` combines the two
directions, with `h81` at universes `.{uF, max uF uV, max uF uW}` and `hS2` at
`.{uF, uV, max uF uW}`. The admissibility hypothesis of the target is not used.

This follows the route of Henniart §3 (printed pages 597-598): §3.3 proves
1.6(b) "exactly as" 1.6(a) in §3.2, from JPSS Theorem 8.1. The proof of (ii) ⇒ (i)
here uses one block of the Langlands datum rather than Henniart's extremal
choice, because the S2 statement already supplies the pole.
