# Support lemmas for the supercuspidal characterization by L-factors of pairs

Author: Worker 1719.
This module, in namespace
`Langlands.RankinSelberg.SupercuspidalLFactorCharacterization`, proves helper
results used by the reduction of Henniart 2002, Théorème 1.6(b) (module
`SupercuspidalLFactorCharacterizationReduction`). It states no new statement;
everything here is proved from published Library results. Throughout, `F` is a
`p`-adic field and `ψ` a `UnitaryAdditiveCharacter` of `F`.

## Supercuspidal representations are generic

- `hasFunctional_of_isSupercuspidal_zero_add`: an irreducible supercuspidal
  representation `A` of `GL_(0+n+1)(F)` has a nonzero Whittaker functional for
  the standard character. The published
  `finrank_generalLinearDerivativePositive_top` says the top derivative of `A`
  is one-dimensional; a nonzero linear form on it, composed with the
  surjective `topQuotient`, is a Whittaker functional
  (`comp_topQuotient_mem_glFunctionals`), and it is nonzero because
  `topQuotient` is surjective.
- `isGeneric_of_isSupercuspidal`: hence (rewriting `0 + n = n`) an irreducible
  supercuspidal representation of `GL_(n+1)(F)` is generic in the published
  sense `IsGeneric ψ n` (irreducible, admissible, with a nonzero Whittaker
  functional); admissibility is part of `IsSupercuspidal`.
- `isOfWhittakerType_of_isSupercuspidal`: so it is of Whittaker type, by the
  published `isOfWhittakerType_of_isGeneric`.

## Langlands data with blocks in a smaller universe

`exists_temperedLanglandsDatum_isLanglandsQuotient`: for topological data `T`
and `n > 0`, every irreducible smooth representation `π` of `GL_n(F)` on a
carrier in `max uF uV` is the Langlands quotient of a tempered Langlands datum
whose blocks have carriers in `uV`. The published
`Classification.temperedLanglandsQuotientCoverage` gives a datum `t` with
blocks in `max uF uV`; `padicIrreducibleSmoothSmallRealization` replaces each
block by an equivalent irreducible block in `uV` (temperedness transfers by
`isTempered_iff_of_equiv`), and the standard modules are equivalent through
`normalizedProductInducedEquiv` with `twistEquiv`, so the Langlands quotient
property transfers by `IsIrreducibleQuotient.of_equiv`.

## Rank casts and L-polynomials

For a representation `X` of `GL_k(F)` and `h : k = N`, `X` transported along
`GeneralLinear.reindex (finCongr h)` keeps irreducibility
(`isIrreducible_comp_reindex_iff`), supercuspidality
(`isSupercuspidal_comp_reindex_iff`) and its rank L-polynomials with any `Z`
(`isPadicRankLPolynomial_comp_reindex_iff`); all three follow by `subst h` and
`comp_reindex_finCongr_rfl` (reindexing along `finCongr rfl` is the identity).
Also:

- `isPadicRankLPolynomial_congr_right`: `IsPadicRankLPolynomial F ψ ν Z X P`
  is invariant under an equivalence of `X` (the published
  `IsPadicSymmetricLPolynomial.congr_equiv` in positive ranks; both sides are
  `False` in rank `0`).
- `IsPadicRankLPolynomial.coeff_zero'`: an L-polynomial of arbitrary ranks has
  constant term `1` (the published `IsPadicSymmetricLPolynomial.coeff_zero`).

## One-block Langlands data

For a tempered Langlands datum `d` of `GL_n(F)` with one block
(`d.shape.length = 1`):

- `singleBlockStandardModuleEquiv`: the standard module of `d` is equivalent
  to its twisted block `ν^(u_i) τ_i`, transported to rank `n` along
  `d.shape.singleBlock_size` (the published `singleBlockNormalizedProductEquiv`).

The downstream reduction reuses the existing one-block lemmas in
[`Classification/RankOneLanglandsStandardModule`](../Classification/RankOneLanglandsStandardModule.md),
in namespace `Langlands.PadicField.TopologicalData.TemperedLanglandsDatum`:

- `standardModule_irreducible_of_length_eq_one`: the standard module is
  irreducible, since its twisted block is irreducible.
- `nonempty_standardModule_equiv_of_length_eq_one`: a Langlands quotient `π`
  of `d` is equivalent to the standard module. The surjective quotient map
  is a nonzero intertwiner from an irreducible representation, hence is
  injective and bijective.
