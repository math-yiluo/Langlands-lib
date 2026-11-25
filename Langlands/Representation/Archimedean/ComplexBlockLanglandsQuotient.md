# The Langlands quotient of a Langlands-ordered complex standard module, from the block statements

Lean module: `Langlands.Representation.Archimedean.ComplexBlockLanglandsQuotient`.

This module is infrastructure for the proof of
`ComplexStandardLanglandsQuotientStatement`. It assembles the block chain
(`ComplexBlockLimit`, `ComplexBlockJacquet`, `ComplexBlockDual`, `ComplexBlockFunctional`,
`ComplexBlockNonvanishing`) into the target statement. Three statements of the Library remain as
hypotheses; none of them is proved here.

* `ComplexBlockChartIntegrableStatement`, proved in `ComplexBlockChartIntegralProof`.
* `ComplexBlockParabolicIntegrationStatement`, proved in `ComplexBlockParabolicIntegrationProof`.
* `ComplexTemperedStandardIrreducibleStatement`, proved in `ComplexTemperedStandardIrreducibleProof`.

## The statement

`ComplexBlockLanglandsQuotientStatement` is the implication

`ComplexBlockChartIntegrableStatement → ComplexBlockParabolicIntegrationStatement →
ComplexTemperedStandardIrreducibleStatement → ComplexStandardLanglandsQuotientStatement`.

The last statement says that for every list `ds` of `n` complex characters in the Langlands order
(`IsComplexLanglandsOrdered`: the real parts of the exponents weakly decrease), the `U(n)`-finite
functions of `complexStandardModule n ds` have a largest proper `(𝔤𝔩_n(ℂ), U(n))`-submodule `R`.
That is, `R` is a proper `IsGKSubmodule` that contains every proper `IsGKSubmodule`.

It is proved as `Langlands.Archimedean.complexBlockLanglandsQuotient`. Applying this theorem to the
proofs of the three hypotheses proves `ComplexStandardLanglandsQuotientStatement`
(`ComplexStandardLanglandsQuotientProof`).

Provenance. Derived: the assembly of the Langlands-lemma argument. No literature statement is
claimed beyond the cited target and hypothesis statements.

## Proof

Unprefixed names are in the namespace `Langlands.Archimedean.ComplexBlockLanglandsQuotient`.

### Block decompositions

`exists_blockOrdered`: if `Re e_{l+1} ≤ Re e_l` for `l + 1 < n`, there is `ks` with
`ComplexBlockFunctional.dim ks = n` and `ComplexBlockFunctional.BlockOrdered ks e`. The proof is
by strong induction on `n`. For `n = m + 1`, let `a` be the least index such that
`Re e_j = Re e_m` for all `a ≤ j ≤ m` (`Nat.find`). This gives a last block `a, …, m`, which is
tied. The strict gap `Re e_a < Re e_{a−1}` follows from the minimality of `a` and the weak order.
Recurse on the first `a` positions.

`exponent_ordered`: the exponents `complexPositionExponent ds` of a Langlands-ordered list are
weakly decreasing.

### Irreducibility of tied principal series

`tiedIrreducible`: `ComplexTemperedStandardIrreducibleStatement` implies
`ComplexBlockFunctional.TiedIrreducible`. Let `ψ` be phase-power characters with exponents `f`
and weights `q`, with tied exponents on `l < b`. Proof:

1. Let `ds = List.ofFn (i ↦ characterOfParams (q i) (f i))` (`ComplexJacquetBorel`).
   `complexPositionCharacter_ofFn_params` gives `complexPositionCharacter ds j = ψ j` for `j < b`,
   using `complexPositionWeight_ofFn` and `complexPositionExponent_ofFn`.
2. The exponents of `ds` all have equal real parts, so the tempered statement gives irreducibility
   for `complexStandardRep b ds`.
3. `principalSeries_congr` shows that the principal series of characters agreeing on the first
   `b` positions coincide. The `(𝔤, K)`-module structures are then transported by
   `isIrreducible_kFinite_congr` (`subst`).

### Assembly

Set `χ = complexPositionCharacter ds`, `e = complexPositionExponent ds` and
`p = complexPositionWeight ds`. `ComplexStrictLanglandsQuotient.isPhasePower` and
`complexPositionCharacter_phase` show that `χ` is phase-power with weights `p`. Take a block
decomposition `ks` from `exists_blockOrdered` and replace `n` by `dim ks`.

* `largestProper N χ`, the sum of all proper `(𝔤, K)`-stable subspaces
  (`ComplexStrictLanglandsQuotient`), lies in `jacKernel`. This is
  `ComplexBlockFunctional.jac_eq_zero_of_proper`, with `TiedIrreducible` from `tiedIrreducible`.
* `ComplexBlockNonvanishing.exists_jac_testVector_ne_zero` gives a test vector `f₀` with
  `jac f₀ ≠ 0`. So `f₀ ∉ largestProper`, and `largestProper` is proper. It is `(𝔤, K)`-stable by
  `isGKStable_largestProper`.
* The submodule `R` of the `U(n)`-finite standard module is the preimage of `largestProper`. The
  remaining steps are as in the published `complexStrictLanglandsQuotient`:
  * `R` is a `(𝔤, K)`-submodule, using `principalSeriesRep_apply_coe` and
    `principalSeriesLie_one_tmul_apply_coe` and splitting tensors `c ⊗ X = c • (1 ⊗ X)`;
  * `R ≠ ⊤` because `f₀ ∉ R`;
  * every proper `(𝔤, K)`-submodule `W` maps to a proper `(𝔤, K)`-stable subspace, hence into
    `largestProper` (`le_largestProper`).
