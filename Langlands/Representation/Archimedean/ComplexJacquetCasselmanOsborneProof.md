# Casselman–Osborne for complex principal series

Lean module: `Langlands.Representation.Archimedean.ComplexJacquetCasselmanOsborneProof`.

## Result

`Langlands.Archimedean.complexJacquetCasselmanOsborne : ComplexJacquetCasselmanOsborneStatement`.

The statement `ComplexJacquetCasselmanOsborneStatement` is defined in
`ComplexStandardJacquetExponentRoute` and is not changed here. For `d : Fin n → ComplexCharacterData`
and a nonzero Jacquet functional `ℓ` on `X(d)` (the `U(n)`-finite functions of
`complexStandardModule n (List.ofFn d)`) with exponents `(a, b)`, it gives permutations `α`, `β`
with `a_j = p(d_{α j}) + q(d_{β j}) + (n - 1) - 2j` and `b_j = i (p(d_{α j}) - q(d_{β j}))`, where
`p(e) = t(e) + l(e)/2`, `q(e) = t(e) - l(e)/2`.

The theorem has no hypotheses beyond those of the statement and uses only the axioms
`propext`, `Classical.choice` and `Quot.sound`.

## Notation

`prodAction π` (Library, `ComplexGenericLargeReduction`) is the action of
`𝔤𝔩_n(ℂ) × 𝔤𝔩_n(ℂ)` obtained from `π` through `ℂ ⊗_ℝ 𝔤𝔩_n(ℂ) ≅ 𝔤𝔩_n(ℂ) × 𝔤𝔩_n(ℂ)`;
`ee π i p q` is the action of the matrix unit `E_pq` of factor `i`, `diagAct π` the action of
polynomials in the diagonal generators `X_(i, a) ↦ ee π i a a`, `annIdeal π` the polynomials
acting into `𝔫V = complexJacquetSubspace n π` (all from the Library module
`ComplexJacquetFinite`). `PQ a b (i, j)` is `P_j = (a_j - i b_j)/2` for `i = 0` and
`Q_j = (a_j + i b_j)/2` for `i = 1`.

## Proof

1. **`trace_scalar_of_inf`, `side_rel_of_inf`.** These are the Library's
   `ComplexJacquetFinite.trace_scalar` and `side_rel`, with the infinitesimal character of
   `prodAction π` as hypothesis in place of irreducibility and admissibility (the proofs are the
   same). Gelfand's central element `tr (E^{(i)})^k` (`Kostant.gel`) acts by a scalar `c`, and
   with `diag_pow` the polynomial `∑_a g_k(a) - c`, in the variables `X_(i, ·)`, lies in
   `annIdeal π`.
2. **`jacquet_kills`, `jacquet_ee`, `jacquet_diagAct`.** A Jacquet functional `ℓ` with exponents
   `(a, b)` vanishes on `𝔫V`, and `ℓ ∘ ee π i j j = PQ a b (i, j) · ℓ`: by
   `ComplexJacquetFinite.prodAction_apply_eq`, `ee π 0 j j` is
   `½(π(1 ⊗ E_jj) - i π(1 ⊗ iE_jj))` and `ee π 1 j j` is `½(π(1 ⊗ E_jj) + i π(1 ⊗ iE_jj))`.
   By induction on polynomials, `ℓ(diagAct π f v) = f(PQ a b) ℓ(v)`.
3. **`gel_sum_eq`.** For two nonzero Jacquet functionals of the same module and each factor
   `i`, applying them to `diagAct π (∑_a g_k(a) - c) v` (which lies in `𝔫V`) at a vector `v`
   where the functional is nonzero gives `∑_a g_k(a)(PQ(i, ·)) = c` for both. So their Gelfand
   sums agree for every `k`.
4. **`complexJacquetCasselmanOsborne`.**
   - `prodAction (complexStandardLie n (List.ofFn d))` has an infinitesimal character:
     `complexStandardLie_hasInfinitesimalCharacter` transported along `tensorLieEquiv`
     (`Kostant.hasInfinitesimalCharacter_comp`).
   - Evaluation at `1` is a Jacquet functional with exponents
     `κ_j(1) = 2t(d_j) + (n - 1) - 2j` and `κ_j(i) = i l(d_j)`
     (`ComplexTemperedComplement.isComplexJacquetFunctional_eval_comp` with the identity map),
     so its coordinates are `P_j = p(d_j) + (n - 1)/2 - j` and `Q_j = q(d_j) + (n - 1)/2 - j`.
     It is nonzero because `ℓ ≠ 0` gives a nonzero function, and a nonzero function has a
     right `U(n)`-translate that is nonzero at `1`
     (`ComplexPermutation.kFiniteEval_one_separating`).
   - `gel_sum_eq` for `ℓ` and evaluation at `1`, in factor `0` and in factor `1`, and
     `GelfandSeparation.exists_perm_of_gel_eq` give permutations `α`, `β` with
     `P_j + j = p(d_{α j}) + (n - 1)/2` and `Q_j + j = q(d_{β j}) + (n - 1)/2`.
   - Then `a_j = P_j + Q_j` and `b_j = i(P_j - Q_j)` (`linear_combination`, using `i² = -1`).

## Provenance

Internal. The statement is the Casselman–Osborne theorem for `X(d)` (central elements act on
the Jacquet module through the Harish-Chandra homomorphism) combined with the value of the
infinitesimal character of `X(d)`. The proof uses Gelfand's central elements instead of the
Harish-Chandra isomorphism: their eigenvalues on lowest-weight functionals are computed by the
Library's recursion, and `ComplexGelfandSeparation` shows that these eigenvalues determine the
shifted coordinates up to permutation.
