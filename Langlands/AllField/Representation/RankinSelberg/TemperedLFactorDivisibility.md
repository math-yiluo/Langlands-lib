# Two-family L-polynomials and their normalized residual, every local field

Module `Langlands.AllField.Representation.RankinSelberg.TemperedLFactorDivisibility`,
namespace `Langlands.AllField.RankinSelberg.TemperedLFactorDivisibility`.

This module is the all-field port of the Library module
`Langlands.Representation.RankinSelberg.TemperedLFactorDivisibility`. The field `F` is
any field with instances `[TopologicalSpace F] [ValuativeRel F]
[IsNonarchimedeanLocalField F]`, so every nonarchimedean local field is covered,
including those of positive characteristic. The canonical data of a p-adic field are
replaced by the data `(⟨⟩ : LocalFieldData F)` of these instances. The statements and
proofs are those of the original with this change.

## Contents

- `symmetricLPolynomial_swap`: the symmetric L-polynomial relation
  `IsPadicSymmetricLPolynomial F ψ ν` (larger rank first, JPSS 1983, (2.12)) is
  invariant under exchanging the two members. In the equal-rank case this is the
  published all-field `isPadicPairLPolynomial_swap_equalRank`.
- `TwoFamilyLPolynomialData F ψ ν m n hm hn π σ`: for two families of blocks
  `π i` of `GL_(m i + 1)(F)` and `σ j` of `GL_(n j + 1)(F)`, a certified polynomial
  `inducedPolynomial` of the two normalized products
  `(⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape m hm) π` and
  `… (succBlockShape n hn) σ`, certified polynomials `blockPolynomial i j` of the pairs
  `(π i, σ j)`, and a normalized residual `D` (`D.coeff 0 = 1`) with
  `∏ i, ∏ j, blockPolynomial i j = D * inducedPolynomial`
  (`TemperedLFactorAlgebra.NormalizedPolynomialQuotient`, a field-free structure of the
  original Library development).
- `nonempty_twoFamilyLPolynomialData`, `twoFamilyLPolynomialData`: such data exist when
  all blocks are of Whittaker type.

## Proof

JPSS 1983, Theorem (3.1)(ii) (printed pages 404–405), is applied twice, through the
published all-field `lFactorMultiplicativity`: once to `Ind(σ)` against the blocks of
`Ind(π)`, giving `X^e ∏ i A i = R P`, and once to each `π i` against the blocks of
`Ind(σ)`, giving `X^f ∏ j Q i j = R' (A i)`. The first-row polynomial is identified with
`A i` by uniqueness. The induced representation of Whittaker type needed for the first
application is the published all-field `normalizedProductWhittakerType`. The normalized
residual is then `NormalizedPolynomialQuotient.of_doubleProduct` of the original
development, which removes the Laurent powers using the constant term one of every
certificate.

Source: H. Jacquet, I. I. Piatetski-Shapiro, J. A. Shalika, *Rankin–Selberg
convolutions*, Amer. J. Math. 105 (1983), 367–464 (literature ID
`jpss-1983-rankin-selberg`), Theorem (3.1), printed pages 404–405.
