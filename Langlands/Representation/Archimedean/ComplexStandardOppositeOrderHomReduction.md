# Reduction of `ComplexStandardOppositeOrderHomStatement` to E and TP

This module was written for the proof of the Library's
`Langlands.Archimedean.ComplexLanglandsQuotientUniqueStatement` (LU).
The module `ComplexLanglandsQuotientUniqueReduction` reduces LU to the Library's
`ComplexLanglandsSubrepresentationStatement` and to the statement Orth,
`ComplexStandardOppositeOrderHomStatement`. This module states one statement,
`ComplexStandardOppositeOrderHomReductionStatement`: E and TP together imply Orth. It also
proves it (`complexStandardOppositeOrderHomReduction`). All declarations are in the namespace
`Langlands.Archimedean`.

The module imports three modules:

- `Langlands.Representation.Archimedean.ComplexStandardHomExponent`, for E
  (`ComplexStandardHomExponentStatement`) and `IsNonnegSimpleRootCombination`;
- `Langlands.Representation.Archimedean.ComplexStandardHomTranspose`, for TP
  (`ComplexStandardHomTransposeStatement`);
- `Langlands.Representation.Archimedean.ComplexLanglandsQuotientUniqueReduction`, for Orth.

## Notation

As in `ComplexStandardHomExponent.md`: for a list `ds` of `n` complex characters, `X(ds)` is
`kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)`, the `U(n)`-finite
functions of the principal series of `ds`. A `ComplexCharacterData` `d` has an integer weight
`l = d.weight` and a complex exponent `t = d.exponent`. Its character is
`z ↦ (z/|z|)^l |z|^{2t}`. `IsComplexLanglandsOrdered ds` says that the real parts of the
exponents of `ds` do not increase along the list.

## Statement: `ComplexStandardOppositeOrderHomReductionStatement`

`ComplexStandardHomExponentStatement → ComplexStandardHomTransposeStatement →
ComplexStandardOppositeOrderHomStatement`.

The three statements are as follows.

- **E** (`ComplexStandardHomExponentStatement`). For all `n`, all `d c : Fin n → ComplexCharacterData`
  and every nonzero intertwining `T : X(List.ofFn d) → X(List.ofFn c)`, there are a permutation
  `σ` of `Fin n` and `u v : Fin n → ℤ` with `IsNonnegSimpleRootCombination u` and
  `IsNonnegSimpleRootCombination v` (all prefix sums `≥ 0`, total `0`) such that, for every `j`,
  `(c j).exponent = (d (σ j)).exponent + (u j + v j)/2` and
  `(c j).weight = (d (σ j)).weight + (u j - v j)`.
- **TP** (`ComplexStandardHomTransposeStatement`). For all `n`, `d`, `c` and every nonzero
  intertwining `T : X(List.ofFn d) → X(List.ofFn c)`, there is a nonzero intertwining
  `T' : X(List.ofFn c⁻¹) → X(List.ofFn d⁻¹)`, where `c⁻¹ j = complexCharacterDataInv (c j)`.
- **Orth** (`ComplexStandardOppositeOrderHomStatement`). For all `n`, lists `ds`, `cs` of length
  `n` and every nonzero intertwining `T : X(ds) → X(cs)`: if `ds` is Langlands-ordered (real parts
  of exponents non-increasing) and the real parts of the exponents of `cs` are non-decreasing,
  then `ds.Perm cs`.

Here "intertwining" means `IsComplexStandardIntertwining` with the target's actions
(`complexStandardRep`, `complexStandardLie`).

**Provenance.** Internal. This implication is the planned formal route to Orth described in
`ComplexLanglandsQuotientUniqueReduction.md` (section "Planned formal route (not provenance)").
It is justified by the proof in this file, which is elementary combinatorics on prefix sums; no
source states it. The mathematical provenance of Orth itself is the separate Badulescu–Renard
argument in that Markdown, and it does not depend on this module. E and TP are the analytic
inputs. They are separate statements, not proved here, with their own provenance in
`ComplexStandardHomExponent.md` and `ComplexStandardHomTranspose.md`. This module proves only
the implication; it proves neither E, TP nor Orth.

## Proof (`complexStandardOppositeOrderHomReduction`)

Let `T : X(ds) → X(cs)` be as in Orth. Write `ds = List.ofFn d` and `cs = List.ofFn c` with
`d c : Fin n → ComplexCharacterData`. Put `x_j = Re (d j).exponent` and
`y_j = Re (c j).exponent`. The hypotheses say that `x` is antitone and `y` is monotone on
`Fin n`.

1. Apply E to `T`. This gives `σ`, `u`, `v` with `y_j = x_{σ j} + w_j/2`, where `w = u + v`.
   Every prefix sum of `w` is `≥ 0` and `∑ w = 0`. So `∑ y = ∑ x`.
2. Apply TP to `T`, and E to the resulting `T' : X(c⁻¹) → X(d⁻¹)`. The exponents of `c⁻¹` and
   `d⁻¹` are `-c_j.exponent` and `-d_j.exponent`. This gives `τ`, `u'`, `v'` with
   `x_j = y_{τ j} - w'_j/2`, where `w' = u' + v'` has all prefix sums `≥ 0`.
3. *Key inequality.* Fix `k ≤ n` and let `P_k = {j : j < k}`. Put `s = σ(P_k)` and
   `t = τ(P_{n-k})`.
   - By step 1, `∑_{P_k} y = ∑_s x + (∑_{P_k} w)/2`.
   - By step 2, `∑_{P_{n-k}} x = ∑_t y - (∑_{P_{n-k}} w')/2 ≤ ∑_t y`.
   - `x` is antitone and `sᶜ` has `n - k` elements, so `∑_{sᶜ} x ≤ ∑_{P_{n-k}} x`
     (`sum_le_sum_finPrefix_of_antitone`).
   - `y` is monotone and `tᶜ` has `k` elements, so `∑_{P_k} y ≤ ∑_{tᶜ} y`
     (`sum_finPrefix_le_sum_of_monotone`).

   Combining these with `∑ x = ∑_s x + ∑_{sᶜ} x` and `∑ y = ∑_t y + ∑_{tᶜ} y` gives
   `∑_{P_k} w ≤ 0`.
4. Every prefix sum of `w = u + v` is therefore `0`. Since the prefix sums of `u` and `v` are
   each `≥ 0`, they are all `0`. So `u = v = 0` (`eq_zero_of_finPrefix_sum_eq_zero`).
5. By E, `c j` and `d (σ j)` then have the same weight and exponent. So they are equal
   (`complexCharacterData_eq_of_weight_exponent`). Hence `c = d ∘ σ`, and
   `List.ofFn d` is a permutation of `List.ofFn (d ∘ σ)` (`Equiv.Perm.ofFn_comp_perm`).

## Auxiliary declarations

- `finPrefix n k : Finset (Fin n)` (an `abbrev`) is the set of `j : Fin n` with `(j : ℕ) < k`.
  This is the index set of the prefix sums in `IsNonnegSimpleRootCombination`.
- `card_finPrefix`: if `k ≤ n` then `(finPrefix n k).card = k`.
- `finPrefix_succ`: `finPrefix n (j + 1) = insert j (finPrefix n j)` for `j : Fin n`.
- `sum_le_sum_finPrefix_of_antitone`: for antitone `x : Fin n → ℝ` and any `s : Finset (Fin n)`,
  `∑_{j ∈ s} x j ≤ ∑_{j ∈ finPrefix n s.card} x j`. Proof: the two sums differ by the sums over
  `s \ P` and `P \ s` (`P` = the prefix), which have the same number of elements. The terms
  over `s \ P` are `≤ x m` and those over `P \ s` are `≥ x m` for `m = s.card - 1`.
- `sum_finPrefix_le_sum_of_monotone`: the same for monotone `y`, with the inequality reversed
  (apply the previous lemma to `-y`).
- `eq_zero_of_finPrefix_sum_eq_zero`: if `∑_{finPrefix n k} u = 0` for all `k ≤ n`, then `u = 0`.
- `complexCharacterData_eq_of_weight_exponent`: two `ComplexCharacterData` with equal weights
  and equal exponents are equal (the character is determined by the defining formula
  `χ(z) = (z/‖z‖)^l ‖z‖^{2t}` of the structure).
