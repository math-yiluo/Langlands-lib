# All-field port of `Langlands.Representation.RankinSelberg.PairLFactor`

`Langlands.AllField.Representation.RankinSelberg.PairLFactor` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.PairLFactor`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.PairLFactor` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**The L-factor of a pair**

For `π` on `GL_(r+1)` and `σ` on `GL_(n+1)` with `n ≤ r`, the L-polynomial of the pair
is the normalized generator of the equal-rank zeta values when `r = n`, and the common
normalized generator of the zeta values of every rectangular block when `n < r`
(JPSS Theorem 2.7(ii)). The L-factor is constructed only from a proof that this
polynomial exists. The relation is invariant under equivalences and determinant
twists, the dual pair uses the inverse-transpose pullbacks and `ψ⁻¹`, and the p-adic
analytic statements supply the existence proof for pairs of Whittaker type.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.AnalyticBridge`

## Declarations

- `Langlands.AllField.RankinSelberg.EqualRankAnalyticStatement.pairLPolynomialExists` (theorem): The p-adic equal-rank analytic statement supplies the L-polynomial of every
  equal-rank pair of Whittaker type, for every compatible quotient measure.
- `Langlands.AllField.RankinSelberg.UnequalRankCommonGeneratorStatement.pairLPolynomialExists` (theorem): The p-adic unequal-rank analytic statements of every block, together with the
  common-generator statement, supply the L-polynomial of every unequal-rank pair of
  Whittaker type.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.exists_coefficientMap_eq_of_surjective`, `Langlands.RankinSelberg.whittakerSet_subset_of_surjective`, `Langlands.RankinSelberg.inverseWhittakerSet_subset_of_surjective`, `Langlands.RankinSelberg.whittakerSet_eq_of_equiv`, `Langlands.RankinSelberg.inverseWhittakerSet_eq_of_equiv`, `Langlands.RankinSelberg.equalRankZetaValues_subset_of_surjective`, `Langlands.RankinSelberg.equalRankZetaValues_eq_of_equiv`, `Langlands.RankinSelberg.unequalRankZetaValues_subset_of_surjective`, `Langlands.RankinSelberg.unequalRankZetaValues_eq_of_equiv`, `Langlands.RankinSelberg.unequalRankZetaValuesAt`, `Langlands.RankinSelberg.unequalRankZetaValuesAt_rfl`, `Langlands.RankinSelberg.unequalRankZetaValuesAt_twist`, `Langlands.RankinSelberg.unequalRankZetaValuesAt_eq_of_equiv`, `Langlands.RankinSelberg.IsPairLPolynomial`, `Langlands.RankinSelberg.PairLPolynomialExists`, `Langlands.RankinSelberg.isPairLPolynomial_of_lt`, `Langlands.RankinSelberg.isPairLPolynomial_self`, `Langlands.RankinSelberg.not_isPairLPolynomial_of_lt`, `Langlands.RankinSelberg.IsPairLPolynomial.isUnequalRankLPolynomial`, `Langlands.RankinSelberg.IsPairLPolynomial.unique`, `Langlands.RankinSelberg.IsPairLPolynomial.coeff_zero`, `Langlands.RankinSelberg.IsPairLPolynomial.ne_zero`, `Langlands.RankinSelberg.pairLPolynomial`, `Langlands.RankinSelberg.pairLPolynomial_spec`, `Langlands.RankinSelberg.pairLPolynomial_eq`, `Langlands.RankinSelberg.pairLFactor`, `Langlands.RankinSelberg.coe_pairLFactor`, `Langlands.RankinSelberg.pairLFactor_eq`, `Langlands.RankinSelberg.pairLPolynomialExists_self_iff`, `Langlands.RankinSelberg.pairLFactor_self`, `Langlands.RankinSelberg.PairLPolynomialExists.unequalRank`, `Langlands.RankinSelberg.pairLFactor_eq_unequalRankLFactor`, `Langlands.RankinSelberg.isPairLPolynomial_congr_equiv`, `Langlands.RankinSelberg.isPairLPolynomial_twist`, `Langlands.RankinSelberg.pairLPolynomialExists_twist_iff`, `Langlands.RankinSelberg.pairLFactor_twist`, `Langlands.RankinSelberg.isPairLPolynomial_smul_measure`, `Langlands.RankinSelberg.IsDualPairLPolynomial`, `Langlands.RankinSelberg.DualPairLPolynomialExists`, `Langlands.RankinSelberg.dualPairLFactor`, `Langlands.RankinSelberg.dualPairLFactor_eq`, `Langlands.RankinSelberg.isDualPairLPolynomial_self`, `Langlands.RankinSelberg.IsDualPairLPolynomial.dualUnequalRank`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
