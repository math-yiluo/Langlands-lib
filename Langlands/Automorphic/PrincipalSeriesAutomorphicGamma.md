# Gamma factors of generic principal-series constituents

Representation-side half of the principal-series pair gamma comparison. All results are
for a `p`-adic field `F`, a nontrivial additive character `ψ`, and a self-dual Haar
measure `ν`. The gamma factor of the full normalized principal series, and then of every
generic irreducible subquotient, is the product of Tate gamma factors of the products of
the inducing characters. This is the multiplicativity of JPSS gamma factors
(Jacquet–Piatetski-Shapiro–Shalika 1983, Theorem 3.1; Henniart 1986, §2.7(iii)),
specialised to Borel inductions.

## Auxiliary results

- `determinant_reindex_symm`: simultaneous reindexing of rows and columns preserves the
  determinant.
- `isSmooth_rankOneCharacter`: `χ ∘ det` on `GL_1` is smooth.
- `principalSeriesZeroEquiv` (internal definition): the one-block normalized principal
  series `principalSeries F 0 μ` is equivalent to `μ 0 ∘ det`. It is obtained from the
  Library's single-block equivalence `singleBlockNormalizedProductEquiv` and the
  determinant reindexing above.
- `principalSeries_isOfWhittakerType`: the normalized principal series is of Whittaker
  type. This is `normalizedProductWhittakerType` with all blocks of rank one.

## Main results

- `isPadicSymmetricGammaFactor_rankOne_principalSeries`:
  `γ(χ × i(μ')) = ∏_j γ_Tate(χ μ'_j)`. *Proof:* gamma multiplicativity
  (`gammaMultiplicativity`) for the Borel block shape gives some factors `G j` whose
  product is a gamma factor of the pair. Uniqueness of symmetric gamma factors
  (`IsPadicSymmetricGammaFactor.unique`) identifies each `G j` with
  `tateRationalGamma F ψ ν (χ * μ' j)`, by `isPadicPairGammaFactor_rankOneCharacters`.
- `isPadicSymmetricGammaFactor_principalSeries_rankOne`:
  `γ(i(μ) × χ) = ∏_i γ_Tate(μ_i χ)`. If `r = 0`, this is the rank-one formula
  transported along `principalSeriesZeroEquiv`. If `r > 0`, the symmetric gamma
  relation for `(i(μ), χ)` unfolds to the one for `(χ, i(μ))`
  (`isPadicSymmetricGammaFactor_of_lt` and `_of_le`), and the previous result applies
  after commuting the products of characters.
- `isPadicSymmetricGammaFactor_principalSeries`:
  `γ(i(μ) × i(μ')) = ∏_j ∏_i γ_Tate(μ_i μ'_j)`. This is again multiplicativity in the
  second variable, combined with the previous result and uniqueness.
- `isAutomorphicPairGammaFactor_principalSeries`: let `A` and `A'` be automorphic
  objects whose representations are generic and are irreducible subquotients of
  `principalSeries F r μ` and `principalSeries F t μ'`. Then
  `∏_j ∏_i tateRationalGamma F ψ ν (μ i * μ' j)` is an
  `IsAutomorphicPairGammaFactor` of their classes. *Proof:* the existence theorems of
  `Global.CuspidalPairFunctionalEquation` provide the class L-polynomials and the
  epsilon factor. These give a class gamma factor `G0` (`automorphicPairGammaFactor`),
  which is a symmetric gamma factor of the generic representatives
  (`isPadicSymmetricGammaFactor_of_generic` with
  `genericLanglandsPairEpsilonFactorComparison`). `componentFactorComparison` says
  that irreducible components share the gamma factor of the ambient smooth induced
  representations. Hence `G0` equals the principal-series product above.
