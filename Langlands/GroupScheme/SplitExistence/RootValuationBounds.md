# Valuation bounds for root elements of a Chevalley group

Author: Worker 1620.

Lean module: `Langlands.GroupScheme.SplitExistence.RootValuationBounds`.

## Content

Throughout, `D` is Chevalley data, `K` a commutative ring, `v : AddValuation K (WithTop ℝ)` and
`θ : X →+ ℝ`.

- `valuation_natCast_nonneg` and `valuation_intCast_nonneg`: integers have nonnegative
  valuation.
- `le_of_forall_le_mul_e_one`: suppose every entry of `s · e_j(1)` has valuation at least `t`.
  Then `v s ≥ t`.
- `NormBound v θ M`: for all basis indices `c, d`, `v (M c d) ≥ θ(wt c - wt d)`.
  - `normBound_one` and `normBound_mul`: the bounded matrices form a multiplicative monoid.
  - `normBound_divExp`: `x_j(s)` is bounded once `v s ≥ θ(root j)`. `divExp_apply` gives the
    entries of `x_j(s)`.
- `ShiftSupport A M`: whenever `M c d ≠ 1 c d`, the difference `wt c - wt d` lies in `A`.
  - `shiftSupport_one` and `shiftSupport_mul`: the latter holds when `A + A ⊆ A`.
  - `shiftSupport_divExp`: requires `k • root j ∈ A` for all `k ≥ 1`.
  - `shiftSupport_listProd`.
- `divExp_mul_apply_of_shiftSupport`. Let `h : X →+ ℤ` be positive on `j`. Let every element of
  `A` have `h`-height at least `h(j)`, with `root j ∉ A`, and let `N` have `ShiftSupport A N`.
  Then for `wt c - wt d = root j` the entry `(x_j(s) N) c d` equals `s · e_j(1) c d`.
- **`le_of_normBound_listProd`**. Take a list `l` of distinct roots, sorted by increasing
  `h`, on which `h` is positive. If `∏_{γ ∈ l} x_γ(w γ)` is `θ`-bounded, then
  `v (w γ) ≥ θ(root γ)` for every `γ ∈ l`.

## Proof

- **Integers.** Induction on natural numbers, using `v(-x) = v(x)`.
- **`le_of_forall_le_mul_e_one`.** The integers `z` with `v(s z) ≥ t` form an ideal of `ℤ`. It
  contains the entries of `e_j(1)`, so by `one_mem_span_e_one` (`RootSubgroupRepresentation`)
  it contains `1`.
- **Multiplicativity.** In `(MN) c d = Σ_u M c u N u d`, each term has valuation at least
  `θ(wt c - wt u) + θ(wt u - wt d) = θ(wt c - wt d)`. Apply `AddValuation.map_le_sum`.
- **Root elements.** A nonzero `e_j(k) c d` forces `wt c - wt d = k • root j` (field
  `e_weight`). Then `v(s^k e) ≥ k v(s) ≥ k θ(root j)`.
- **Shift supports.** Expand `MN = M + N - 1 + (M - 1)(N - 1)`.
- **Head entry.** In `Σ_u x_j(s) c u N u d`, a term with `u ≠ d` would need
  `wt u - wt d ∈ A`, which has height at least `h(j)`. If `u = c`, this contradicts
  `root j ∉ A`. Otherwise `wt c - wt u` is `k • root j` with `k ≥ 1`, and the total height would
  be at least `2h(j)`. So only `u = d` remains, with `N d d = 1`. Comparing heights shows that
  only the `k = 1` term of `x_j(s) c d` survives.
- **Peeling.** Let `γ` be the head of the list. Take
  `A = {x | h(γ) < h(x)} ∪ {roots of the rest of the list}`; then `A + A ⊆ A`. The product of
  the rest has `ShiftSupport A`, so the head-entry lemma identifies the entries of the product
  over the weight difference `γ`. Boundedness gives `v(w γ · e_γ(1) c d) ≥ θ(γ)`, hence
  `v(w γ) ≥ θ(γ)`. Multiplying on the left by the bounded element `x_γ(-w γ)` gives a bounded
  product of the rest of the list, and induction finishes the proof.

## Provenance

Internal. From the published `ChevalleyData`, the proofs use only the definition `divExp` and
the fields `e_zero` and `e_weight`, together with `one_mem_span_e_one`. The bounds serve as a
substitute for explicit commutator structure constants in the proof of axiom V 3
(`ChevalleyRootFamilyCommutator`).
