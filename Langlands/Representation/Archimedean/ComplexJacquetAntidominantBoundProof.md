# The weight bound for antidominant Jacquet exponents

Lean module: `Langlands.Representation.Archimedean.ComplexJacquetAntidominantBoundProof`.

## Result

`Langlands.Archimedean.complexJacquetAntidominantBound : ComplexJacquetAntidominantBoundStatement`.

The statement is defined in `ComplexStandardJacquetExponentRoute` and is not changed here. Let
`ℓ ≠ 0` be a Jacquet functional on `X(d)` with exponents `(a, b)`, where `b_j = i w_j` for
integers `w_j ≤ 0` that do not increase with `j`, and `Re a_j + 2j` is strictly increasing in
`j`. Then `∑_j |l(d_j)| ≤ ∑_j |w_j|`. The proof shows more: every `l(d_j) ≤ 0` and
`∑_j l(d_j) = ∑_j w_j`, so equality holds.

The theorem has no hypotheses beyond those of the statement and uses only the axioms
`propext`, `Classical.choice` and `Quot.sound`.

Notation: `X(d)` (`KX d`) is the space of `U(n)`-finite functions of
`complexStandardModule n (List.ofFn d)`. `complexCharacterDataInv` (`c ↦ c⁻¹`) negates weight
and exponent. Declarations without prefix are in `Langlands.Archimedean.JacquetAntidominantBound`.

## Weights from a fixed vector

- `complexPositionWeight_eq_zero`: if all weights of a list vanish, so do all its position
  weights.
- `borelFactor_of_norm_one`: for `|z| = 1`, `borelFactor l α z = z^l`.
- `character_eq_one_of_fixed`: let `F ≠ 0` in `X(d)` be fixed by `U(n)`. Then
  `F(k) = F(1) ≠ 0` on `U(n)` (otherwise `F = 0`,
  `ComplexDuality.eq_zero_of_mem_principalSeries_of_eqOn`). Evaluating `F` at the unitary diagonal
  matrix of the phases of `a` (`ComplexPartialJacquet.phaseMatrix_toUnits`) shows that the
  principal-series character is `1` at these phases.
- `exists_unit_zpow_eq_neg_one`: for `l ≠ 0`, `z = exp(iπ/l)` has `|z| = 1` and `z^l = -1`.
- `weight_eq_zero_of_character`: if the character is `1` at all phases, every weight vanishes.
  If `l(d_j) ≠ 0`, take the phase `z` above at position `j` and `1` elsewhere; by
  `principalSeriesCharacter_ofFn` the character there is `z^{l(d_j)} = -1`.

## The spherical case

`weight_eq_zero_of_intertwining`: let `T' : X(c') → X(d')` be a nonzero intertwining map. Assume
all weights of `c'` vanish and the real parts of the exponents of `c'` strictly decrease. Then
all weights of `d'` vanish. Notation: `χ, e` are the position characters and exponents of `c'`
(`ComplexStrictLanglandsQuotient.isPhasePower`); their phases are trivial
(`complexPositionCharacter_phase`).
1. **Spherical vector.** `complexPrincipalSeriesExtension` of the constant function `1` on
   `U(n)` gives `φ ∈ X(c')` with `φ = 1` on `U(n)`. Its equivariance under the diagonal phases
   holds because the character is trivial on phases.
2. **Kernel.** `ker T'`, as a space of functions, is stable under right translation by `U(n)`
   (`IsComplexStandardIntertwining.map_rep`) and under right derivatives (`map_lie`), and it is
   proper (`T' ≠ 0`). By the Library's `complexJacquetKernel` the Jacquet integral vanishes on
   it.
3. `jacquet n φ ≠ 0` (`ComplexSphericalJacquetNormalized.jacquet_ne_zero_of_spherical`), so `T' φ ≠ 0`.
4. `φ` is `U(n)`-fixed (both sides are in the principal series and agree on `U(n)`,
   `JacquetTranslation.eq_of_eq_unitary`), hence so is `T' φ`. The previous section gives the
   claim.

`weight_eq_zero_of_spherical`: let `ℓ ≠ 0` be a Jacquet functional on `X(d)` with exponents
`(a, 0)` and `Re a_j + 2j` strictly increasing. Then all weights of `d` vanish.
- Frobenius reciprocity (`complexJacquetFrobenius` with `isComplexGKModule_complexStandardModule`)
  gives `c` with `2t(c_j) + (n - 1) - 2j = a_j`, `i l(c_j) = b_j = 0`, and a nonzero embedding
  `B : X(d) → X(c)`.
- `ComplexPermutation.intertwining_of_embedding` and `complexStandardHomTranspose` give a nonzero
  intertwining map `T' : X(c⁻¹) → X(d⁻¹)`.
- `c⁻¹` has zero weights, and its exponents `-t(c_j)` have strictly decreasing real parts:
  `Re t(c_j) = (Re a_j + 2j - (n - 1))/2` strictly increases
  (`ComplexBlockLanglandsQuotient.complexPositionExponent_ofFn`).
- `weight_eq_zero_of_intertwining` gives `l(d_j⁻¹) = -l(d_j) = 0`.

## The general case

`weight_nonpos`: under the hypotheses of the bound, every `l(d_j) ≤ 0`. Strong induction on
`N = ∑_j (-w_j)`:
- If all `w_j = 0`, then `b = 0` and the spherical case applies.
- Otherwise let `j₀` be the first index with `w_{j₀} < 0`. Since `w` does not increase,
  `w_j < 0` exactly for `j ≥ j₀`, i.e. for the last `k = n - j₀` positions.
- The translation theorem `complexJacquetTranslation` with this `k` and `ε = 1` gives `d'` with
  `l(d'_j) = l(d_j) + [j ∈ S]` and a nonzero Jacquet functional `ℓ'` with exponents
  `a_j + λ_j`, `b_j + iλ_j`, where `λ` is the indicator of the last `k` positions.
- `w' = w + λ` is again `≤ 0` and nonincreasing, `Re(a_j + λ_j) + 2j` is still strictly
  increasing, and `∑_j (-w'_j) < N`.
- By induction `l(d'_j) ≤ 0`, hence `l(d_j) ≤ 0`.

`complexJacquetAntidominantBound`:
- By Casselman–Osborne (`complexJacquetCasselmanOsborne`),
  `∑_j b_j = i(∑_j p(d_{α j}) - ∑_j q(d_{β j})) = i ∑_j l(d_j)` (reindexing by `α`, `β`).
  So `∑_j l(d_j) = ∑_j w_j`.
- Since all `l(d_j) ≤ 0` and all `w_j ≤ 0`,
  `∑_j |l(d_j)| = -∑_j l(d_j) = -∑_j w_j = ∑_j |w_j|`.

## Provenance

Internal. Classically, a nonzero map from `X(d)` into an antidominant principal series has
image containing the lowest `U(n)`-type, whose weights bound those of `d`. The implemented proof
avoids lowest `U(n)`-types. It reduces to the spherical case by translation and there uses only
the Library's Jacquet-integral kernel theorem and the explicit nonvanishing of the spherical
Jacquet integral.
