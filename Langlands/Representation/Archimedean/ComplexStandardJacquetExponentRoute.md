# A route to the exponent shape of Jacquet functionals on complex principal series

Lean module: `Langlands.Representation.Archimedean.ComplexStandardJacquetExponentRoute`
(namespace `Langlands.Archimedean`; helper lemmas in
`Langlands.Archimedean.JacquetExponentRoute`). Worker 761 wrote it for Task 7179
(`be6e152c-5dbf-4acb-b0eb-1d68bd50d53c`), the proof of the Library statement
`Langlands.Archimedean.ComplexStandardJacquetExponentStatement` (JE, module
`ComplexStandardHomExponentJacquetReduction`).

The module contains

* three propositions about the `U(n)`-finite principal series of `GL_n(ℂ)`, none of them proved
  here: `ComplexJacquetCasselmanOsborneStatement` (CO), `ComplexJacquetTranslationStatement`
  (Trans) and `ComplexJacquetAntidominantBoundStatement` (Bound);
* the proposition `ComplexStandardJacquetExponentRouteStatement`, which is
  `CO → Trans → Bound → JE`;
* the theorem `complexStandardJacquetExponentRoute`, which proves it, with helper lemmas.

So JE is reduced to CO, Trans and Bound. The reduction uses no analysis and no
automatic-continuity theorem. The three propositions are proved in the separate modules
`ComplexJacquetCasselmanOsborneProof`, `ComplexJacquetTranslationProof` and
`ComplexJacquetAntidominantBoundProof`, and JE itself in `ComplexStandardJacquetExponentProof`.

## Notation

As in `ComplexStandardHomExponentJacquetReduction.md`:

* a `ComplexCharacterData` `e` is the character `z ↦ (z/‖z‖)^{l} ‖z‖^{2t}` of `ℂˣ`, with weight
  `l = e.weight : ℤ` and exponent `t = e.exponent : ℂ`. Its holomorphic and antiholomorphic
  coordinates are `p(e) = t + l/2` and `q(e) = t - l/2`, so that the character is
  `z ↦ z^{p} z̄^{q}`;
* for `d : Fin n → ComplexCharacterData`, `X(d)` is
  `kFiniteFunctions (complexStandardModule n (List.ofFn d)) (unitaryCompact ℂ n)` with the Lie
  algebra action `complexStandardLie n (List.ofFn d)`;
* `IsComplexJacquetFunctional n π ℓ a b` (module `ComplexJacquetReduction`): `ℓ` vanishes on
  `π(1 ⊗ X) V` for strictly upper triangular `X`, and `ℓ ∘ π(1 ⊗ E_jj) = a_j ℓ`,
  `ℓ ∘ π(1 ⊗ i E_jj) = b_j ℓ`. We call `(a, b)` the exponents of `ℓ`;
* `IsNonnegSimpleRootCombination u` (module `ComplexStandardHomExponent`): all prefix sums of
  `u : Fin n → ℤ` are `≥ 0` and the total is `0`, i.e. `u ∈ ℕ·Δ`.

Evaluation at the identity on `X(d)` has exponents `a_j = 2 t(d_j) + (n - 1) - 2j`,
`b_j = i l(d_j)`. For a Jacquet functional with exponents `(a, b)` put
`P_j = (a_j - i b_j)/2` and `Q_j = (a_j + i b_j)/2`; then `a_j = P_j + Q_j`,
`b_j = i (P_j - Q_j)`, and for evaluation at `1` one has `P_j = p(d_j) + ρ_j`,
`Q_j = q(d_j) + ρ_j` with `ρ_j = (n - 1)/2 - j`. In these terms JE says: there is one
permutation `σ` with `P_j - ρ_j = p(d_{σ j}) + u_j` and `Q_j - ρ_j = q(d_{σ j}) + v_j`,
`u, v ∈ ℕ·Δ`.

## The three statements

### CO: `ComplexJacquetCasselmanOsborneStatement`

For every `n`, `d : Fin n → ComplexCharacterData`, linear `ℓ : X(d) → ℂ` and `a b : Fin n → ℂ`
with `ℓ ≠ 0` and `IsComplexJacquetFunctional n (complexStandardLie n (List.ofFn d)) ℓ a b`, there
are permutations `α β : Equiv.Perm (Fin n)` with, for every `j`,

* `a j = p(d (α j)) + q(d (β j)) + ((n : ℂ) - 1) - 2 j`, and
* `b j = i (p(d (α j)) - q(d (β j)))`,

where `p(e) = e.exponent + e.weight / 2` and `q(e) = e.exponent - e.weight / 2` are written out in
the Lean statement. Equivalently `P_j - ρ_j = p(d_{α j})` and `Q_j - ρ_j = q(d_{β j})`: the
holomorphic coordinates of the exponents of `ℓ` are a permutation of those of `d`, and so are the
antiholomorphic ones, possibly by a different permutation.

Provenance: derived, internal. This is the form, for the principal series of `GL_n(ℂ)`, of the
Casselman–Osborne theorem (the centre of `U(𝔤_ℂ)`, `𝔤_ℂ ≅ 𝔤𝔩_n × 𝔤𝔩_n`, acts on the Jacquet module
through the Harish-Chandra homomorphism) combined with the value of the infinitesimal character
of `X(d)`. No cited source states it in this form. The Library proves that `X(d)` has an
infinitesimal character (`complexStandardLie_hasInfinitesimalCharacter`) but not its value.
CO allows `α ≠ β`; the `GL_2(ℂ)` example "a weight that JE excludes" in
`ComplexStandardHomExponentJacquetReduction.md` satisfies CO with `α ≠ β`.

### Trans: `ComplexJacquetTranslationStatement`

For every `n`, `d`, `ℓ ≠ 0` with `IsComplexJacquetFunctional … ℓ a b`, every `k ≤ n` and every
`ε ∈ {1, -1}`, there are a `k`-element set `S ⊆ Fin n`, characters `d'` and a linear
`ℓ' : X(d') → ℂ` with

* `(d' j).weight = (d j).weight + ε` and `(d' j).exponent = (d j).exponent + 1/2` for `j ∈ S`,
  and `d' j` has the weight and exponent of `d j` for `j ∉ S`. So `d'` is `d` with the
  holomorphic coordinate `p` (if `ε = 1`) or the antiholomorphic coordinate `q` (if `ε = -1`)
  raised by `1` at the positions of `S`;
* `ℓ' ≠ 0` and `IsComplexJacquetFunctional n (complexStandardLie n (List.ofFn d')) ℓ' a' b'` with
  `a'_j = a_j + λ_j`, `b'_j = b_j + i ε λ_j`, where `λ_j = 1` if `n ≤ j + k` and `λ_j = 0`
  otherwise. So `λ = e_{n-k} + ⋯ + e_{n-1}` is the lowest weight of `Λ^k ℂ^n`, and `P` (if
  `ε = 1`) or `Q` (if `ε = -1`) moves by `λ`.

Provenance: derived, internal. It is the translation principle (tensoring with a
finite-dimensional representation) for Jacquet functionals. Let `F = Λ^k ℂ^n`, as a
holomorphic (`ε = 1`) or antiholomorphic (`ε = -1`) representation of `GL_n(ℂ)`, and let `f*` be
its lowest-weight linear form, which vanishes on `𝔫 F` and has weight `λ`. Then `ℓ ⊗ f*` is a
nonzero Jacquet functional on `X(d) ⊗ F` with exponents `(a', b')`. As a `(𝔤, K)`-module,
`X(d) ⊗ F` is the `U(n)`-finite induced module from `B` of `χ_d δ^{1/2} ⊗ F|_B`, and a
`B`-stable filtration of `F` with one-dimensional quotients of weights `e_S` (`|S| = k`)
filters it by the principal series `X(d + e_S)`. The first step of the filtration on which
`ℓ ⊗ f*` does not vanish gives `S` and `ℓ'`. No cited source states it in this form.

### Bound: `ComplexJacquetAntidominantBoundStatement`

For every `n`, `d`, `ℓ ≠ 0` with `IsComplexJacquetFunctional … ℓ a b`, and every
`w : Fin n → ℤ` such that

* `b j = i w j` for all `j`,
* `w j ≤ 0` for all `j`, and `w j ≤ w i` whenever `i ≤ j` (`w` is nonpositive and does not
  increase),
* `Re a_i + 2i < Re a_j + 2j` whenever `i < j`,

one has `∑_j |(d j).weight| ≤ ∑_j |w j|`.

Meaning. Let `c` be the characters attached to `(a, b)` (`2 t(c_j) + (n - 1) - 2j = a_j`,
`l(c_j) = w_j`); by Frobenius reciprocity (`complexJacquetFrobenius`) these are the
characters of a principal series `X(c)` that receives a nonzero `(𝔤, K)`-map from `X(d)`. The
hypotheses say that `Re t(c_j)` strictly increases (`c` is in the antidominant chamber, the
opposite of the Langlands order), and that `-l(c)` is nonnegative and nondecreasing. The
conclusion bounds the size of the `M ∩ K`-type `l(d)` of `X(d)` by that of `X(c)`.

Provenance: derived, internal. The intended proof: the transpose `X(c⁻¹) → X(d⁻¹)`
(`complexStandardHomTranspose`) is nonzero and its kernel is a proper submodule of the strictly
dominant principal series `X(c⁻¹)`, so it lies in the kernel of the Jacquet integral
(`complexJacquetKernel`). The `U(n)`-finite function of `X(c⁻¹)` whose restriction to `U(n)` is
`∏_j L_j(κ)^{m_j}` (with `L_j` the minor of the bottom `j + 1` rows and last `j + 1` columns and
exponents `m_j ≥ 0` determined by `-l(c)`) has degree `∑_j |l(c_j)|` as a polynomial on `U(n)`
and a nonzero Jacquet integral, computed stage by stage. Its image in `X(d⁻¹)` is nonzero and is
a polynomial of degree at most `∑_j |l(c_j)|` on `U(n)`, while every nonzero function of `X(d⁻¹)`
has degree at least `∑_j |l(d_j)|` on `U(n)`. No cited source states it in this form.

## The route: `ComplexStandardJacquetExponentRouteStatement`

`ComplexStandardJacquetExponentRouteStatement` is
`ComplexJacquetCasselmanOsborneStatement → ComplexJacquetTranslationStatement →
ComplexJacquetAntidominantBoundStatement → ComplexStandardJacquetExponentStatement`.

Provenance: derived, internal (the route of Task 7179).

## Proof of the route (`complexStandardJacquetExponentRoute`)

All results below are proved, using only the standard axioms.

### The cone (`JacquetExponentRoute.cone_*`)

* `cone_zero`, `cone_add`: `ℕ·Δ` contains `0` and is closed under addition.
* `cone_indicator`: for a `k`-element set `T ⊆ Fin n`, the vector
  `j ↦ [j ∈ T] - [n ≤ j + k]` lies in `ℕ·Δ`. Its prefix sum up to `m` is
  `#{j ∈ T, j < m} - #{j < m, n ≤ j + k}`. The second number is `min n m - min m (n - k)`
  (from `Fin.card_filter_val_lt`), and the first is at least `k - min k (n - min n m)`, since at
  most `n - min n m` elements of `T` lie at positions `≥ m`. The total is `k - k = 0`.

### Iterated translation (`pos_iff_of_monotone`, `translate_mono`)

* `pos_iff_of_monotone`: if `lam : Fin n → ℕ` is monotone and `k` is the number of positions
  where it is positive, then `lam j > 0` exactly when `n ≤ j + k`. The zero positions form a
  down-set, and comparing cardinalities with `Fin.card_filter_val_lt` locates its boundary.
* `translate_mono`: given Trans, `ε = ±1` and a monotone `lam : Fin n → ℕ`, every nonzero Jacquet
  functional `ℓ` on `X(d)` with exponents `(a, b)` yields `d'`, a nonzero Jacquet functional
  `ℓ'` on `X(d')` with exponents `a + lam`, `b + i ε lam`, and `μ : Fin n → ℕ` with
  `l(d') = l(d) + ε μ`, `t(d') = t(d) + μ/2`, and `σ·μ - lam ∈ ℕ·Δ` for every permutation
  `σ` (`(σ·μ)_j = μ_{σ j}`). Proof by strong induction on `∑ lam`: if `lam = 0` take
  `ℓ' = ℓ`. Otherwise apply Trans with `k` the number of positive entries, so that
  `λ = lam - lam'` with `lam' = lam - [n ≤ · + k]` monotone of smaller sum, and apply the
  induction hypothesis to `lam'`. The new `μ` is the old one plus the indicator of `S`, and the
  cone condition follows from `cone_add` and `cone_indicator` applied to `σ⁻¹(S)`.

### The main argument

Let `ℓ ≠ 0` be a Jacquet functional on `X(d)` with exponents `(a, b)`.

1. `IsComplexJacquetFunctional.exists_weight` (module `ComplexJacquetTorus`) gives integers `w0`
   with `b_j = i w0_j`.
2. Constants independent of the translation size: `K = ∑_{i,j} |w0_i - w0_j|`,
   `C = ∑_j |w0_j|`, `ψ_j = w0_j + K j + C` (nonnegative and nondecreasing),
   `A_j = (a_j - (n - 1) + 2j + w0_j)/2` and `B_j = (a_j - (n - 1) + 2j - w0_j)/2` (so
   `A_j = P_j - ρ_j` and `B_j = Q_j - ρ_j`), `B₁ = ∑_{i,j} |Re a_i - Re a_j|`,
   `B₂ = ∑_{i,y} ‖A_i - B_y - ψ_y‖` and `D = ∑_j (K j + C)`. Choose
   `M = ⌈B₁ + D + B₂⌉₊ + 1`.
3. `translate_mono` with `ε = 1`, `lam_j = M j`, then with `ε = -1`, `lam_j = M j + ψ_j`, gives
   `d₂`, a nonzero Jacquet functional `ℓ₂` on `X(d₂)` with exponents
   `a₂_j = a_j + 2 M j + ψ_j`, `b₂_j = i (w0_j - ψ_j)`, and `μ₁`, `μ₂` with
   `p(d₂) = p(d) + μ₁`, `q(d₂) = q(d) + μ₂`, `σ·μ₁ - M j ∈ ℕ·Δ` and
   `σ·μ₂ - (M j + ψ_j) ∈ ℕ·Δ` for all `σ`.
4. Bound applies to `ℓ₂` with `w_j = w0_j - ψ_j = -(K j + C)`: it is nonpositive and does not
   increase, and `Re a₂_j + 2j = Re a_j + 2 M j + ψ_j + 2j` strictly increases because
   `M > B₁`. Hence `∑_x |l(d₂ x)| ≤ D`.
5. CO applied to `ℓ₂` gives `α`, `β`. From its two equations, `b₂ = i (w0 - ψ)` and
   `a₂ = a + 2 M j + ψ` one gets `p(d₂ (α j)) = A_j + M j` and `q(d₂ (β j)) = B_j + M j + ψ_j`
   (`linear_combination`). Therefore
   `l(d₂ x) = M (α⁻¹ x - β⁻¹ x) + (A_{α⁻¹ x} - B_{β⁻¹ x} - ψ_{β⁻¹ x})`.
6. `α = β`. Otherwise some `x₀` has `α⁻¹ x₀ ≠ β⁻¹ x₀`, so `∑_x M |α⁻¹ x - β⁻¹ x| ≥ M`, while
   `∑_x ‖A_{α⁻¹x} - B_{β⁻¹x} - ψ_{β⁻¹x}‖ ≤ B₂` (reindex by `α`). The triangle inequality gives
   `∑_x |l(d₂ x)| ≥ M - B₂ > D`, contradicting step 4.
7. With `σ = α = β`, `u_j = μ₁(σ j) - M j` and `v_j = μ₂(σ j) - (M j + ψ_j)` lie in `ℕ·Δ`
   by step 3, and step 5 gives `A_j = p(d_{σ j}) + u_j`, `B_j = q(d_{σ j}) + v_j`. Since
   `a_j = A_j + B_j + (n - 1) - 2j` and `b_j = i (A_j - B_j)`, these are the two equations of JE
   (`linear_combination` again, using `t = (p + q)/2`, `l = p - q`).

## Use

Once CO, Trans and Bound are proved, JE is `complexStandardJacquetExponentRoute hCO hTr hB`,
and the Library's `ComplexStandardHomExponentStatement` follows by
`complexStandardHomExponentJacquetReduction`.
