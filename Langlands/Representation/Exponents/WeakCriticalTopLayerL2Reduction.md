# Square-integrability of quotients of the maximal layer: reduction

Module `Langlands.Representation.Exponents.WeakCriticalTopLayerL2Reduction`,
author Worker 728. It proves the published statement
`Langlands.GLWeaklyCriticalTopLayerL2Statement.{uF,uV,uW}` from one proposition
hypothesis, `GLProductLeviDualOppositeSquareIntegrableSufficiencyStatement.{uF,uW}`.
That is the dual-opposite form of the product-Levi square-integrability criterion
(statement task `87919e1e-88f0-4422-9ab7-08a57f71932d`). Every other input is a
proved Library theorem.

The theorem is `Langlands.glWeaklyCriticalTopLayerL2_of`. Its inspection uses
only the axioms `propext`, `Classical.choice` and `Quot.sound`. Mathematically it
is the analytic part of the proof of Silberger 1979, Corollary 4.5.11 (printed
pp.189–190). There,
Theorem 4.5.10 (the `L²` criterion) is applied to a quotient of the maximal
layer of Corollary 2.4.2, and weak criticality excludes the boundary case.

## Auxiliary lemmas

- `norm_blockPrefix_character`: let `s` be the real part of `ψ` and `u` a unit.
  The flattened block scalar equal to `u` on the inner blocks `0..i` of outer
  block `j`, and to `1` elsewhere, has `‖ψ‖` equal to
  `|u| ^ (∑ i' ≤ i, s (j, i'))`. The proof uses the Library's
  `sum_filter_flattenOuter_le`.
- `norm_comp_splitIndex_eq_one`: suppose `‖χ‖ = 1`, `ψ (c ∘ flattenOuter) = χ c`,
  and the prefix of block `j` up to `i` vanishes. Then `ψ` composed with
  `splitIndex D j i` is unitary. Every split block scalar `c ∘ splitIndex` is an
  outer block scalar (taking the values of the second half of block `j`) times
  the scalar of the previous item with `u = c_first / c_second`.

## Proof of `glWeaklyCriticalTopLayerL2_of`

1. **Coordinate transport.** `(ConjugateBlockPair.standard C).pullbackRep A = A`
   for every `C`: conjugation by the identity matrix, proved by `congr` and
   `simp`, not assumed definitionally. The unitary part of the critical
   predicate gives `‖χ a‖ = 1`. `A` is admissible (`IsTempered.isAdmissible`).
2. **Applying the criterion.** For each Haar measure the consumer form is
   applied to `C = B`, `ω = χ` and `S`. It remains to check its exponent
   hypothesis for every refinement `D`, character `ψ`, real part `s` and
   eigenfunctional `φ`.
3. **Exponent of the source.** `topLayer_flattened_dual` (module
   `WeakCriticalTopLayerExponents`) is applied with `k = d - 1`. It gives
   `ψ (c ∘ flattenOuter) = χ c`, that `ψ` is a dual exponent of `A` along
   `B.flatten D`, and a generalized `ψ`-vector `L` with
   `(ρ (a ∘ flattenOuter) - χ a) ^ (d - 1) L ≠ 0`.
4. **Weak prefixes.** The block totals of `s` vanish (Library
   `sum_fibre_eq_zero_of_unitary`). The bound
   `norm_le_one_of_isDualJacquetExponent_of_isTempered` along `B.flatten D` gives
   nonpositive global prefixes
   (`ScalarLayer.prefix_nonpos_of_antitone_bound`), hence nonpositive prefixes
   inside each block (`ScalarLayer.blockPrefix_nonpos_of_global`).
5. **Strict proper prefixes.** Suppose the prefix of block `j` up to a
   non-final inner block `i` vanishes. Let `C' = B.splitShape D j i _` (module
   `WeakCriticalTopLayerSplit`) and `ψ' = ψ ∘ splitLabel`. Then:
   - `ψ'` is a dual exponent of `A` along `C'` (`isDualJacquetExponent_coarsen`)
     and unitary (`norm_comp_splitIndex_eq_one`);
   - the standard pair of `C'` strictly refines that of `B`
     (`standard_splitShape_strictlyRefines`; `F` is infinite, being an algebra
     over `ℚ_p`);
   - `ψ'` extends `χ` (`characterExtends_iff`; the block scalar of `B` at `c`
     is the block scalar of `C'` at `c ∘ splitMergeLabel`, and
     `splitMergeLabel ∘ splitLabel = flattenOuter`);
   - the nilpotence index of `ψ'` along `C'` is at least `d`. If it were at
     most `d - 1`, the restriction of `L` (module
     `WeakCriticalTopLayerCoarsening`) would be killed by the `(d - 1)`-st power
     of the defect of `a ∘ splitMergeLabel`. Its preimage
     `(ρ (a ∘ flattenOuter) - χ a) ^ (d - 1) L` would then be zero, because the
     restriction is injective.

   Weak criticality at this pair gives an index `< d`, contradicting the last
   point. So proper prefixes are strictly negative.

## Imports and independence

Besides the statement file of the hypothesis, the proof uses the Library's
dual-Jacquet, inheritance, transitivity, flattened-comparison, finiteness and
coarsening results. It also uses the product-Levi tempered necessity theorem
`glProductLeviTemperedExponentNecessity`. From
`Classification/TemperedOppositeJacquetScalarLayerAssembly` it uses the reversal
and upper-bound lemmas and the two arithmetic lemmas named above, but not the
scalar-layer assembly itself. It uses no support, exhaustion, minimality,
unitarity or genericity theorem. The import closure contains no proof module of
the routes forbidden by task `ecd53630`.
