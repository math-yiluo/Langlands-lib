# The lattices `ϖ ^ k R` of a compact open order

The module `Langlands.HarmonicAnalysis.UnitConjugation.OrderLevels` provides the scale of
lattices `ϖ ^ k R`, `k ∈ ℤ`, attached to a compact open subring `R` of an algebra `A` over a
nonarchimedean local field `F` and an element `ϖ ∈ F` with `0 < |ϖ| < 1`. They replace a norm on
`A` in the proof of Howe's finiteness theorem: membership in `ϖ ^ k R` plays the role of
`‖x‖ ≤ |ϖ| ^ k`. All declarations are in the namespace
`Langlands.HarmonicAnalysis.UnitConjugation`; `valuation F` is the valuation of the valuative
relation of `F`.

## Algebraic part

For a field `F` with `[ValuativeRel F]`, an `F`-algebra `A`, a subring `R` and `ϖ : F`:

- `orderLevel R ϖ k : AddSubgroup A` is the preimage `{x | ϖ ^ (-k) • x ∈ R}` for arbitrary
  `ϖ` (`mem_orderLevel`). At `k = 0` it is `R` as an additive subgroup (`mem_orderLevel_zero`).
  For `ϖ ≠ 0`, this preimage equals the scalar multiple `ϖ ^ k R` because the scalar actions
  of `ϖ ^ k` and `ϖ ^ (-k)` are inverse.
- `smul_mem_orderLevel`: if `R` is stable under the integers of `F`
  (`c • x ∈ R` whenever `valuation F c ≤ 1`), each `orderLevel R ϖ k` is too.
- With `ϖ ≠ 0`:
  - `orderLevel_anti`: for `R` stable under the integers and `valuation F ϖ < 1`, the lattices
    decrease: `k ≤ l` implies `ϖ ^ l R ⊆ ϖ ^ k R`;
  - `zpow_smul_mem_orderLevel_iff`: `ϖ ^ j • x ∈ ϖ ^ (k + j) R ↔ x ∈ ϖ ^ k R`;
  - `mul_mem_orderLevel`: `ϖ ^ a R · ϖ ^ b R ⊆ ϖ ^ (a + b) R`, and its special cases
    `mul_mem_orderLevel_left`, `mul_mem_orderLevel_right` (each lattice is a two-sided
    `R`-module).

## Topological part

Now `F` is a nonarchimedean local field (`[TopologicalSpace F] [IsNonarchimedeanLocalField F]`)
and `A` carries its module topology (`[TopologicalSpace A] [IsModuleTopology F A]`).

- `tendsto_pow_atTop_nhds_zero_of_valuation_lt_one`: `ϖ ^ n → 0` when `valuation F ϖ < 1`. Proof:
  the sets `{x | valuation F x < γ}` form a basis of neighbourhoods of `0`
  (`IsValuativeTopology.hasBasis_nhds_zero`), and the value group is archimedean
  (`exists_pow_lt₀`).
- `IsCompactOpenOrder F R` (a structure): `R` is compact, open, and stable under the integers
  of `F`.

Assume `IsCompactOpenOrder F R`, `ϖ ≠ 0` and `valuation F ϖ < 1` (each statement uses only the
hypotheses its proof needs).

- `isOpen_orderLevel`: `ϖ ^ k R` is the preimage of `R` under `x ↦ ϖ ^ (-k) • x`, hence open.
- `isCompact_orderLevel`: `ϖ ^ k R` is the image of `R` under `x ↦ ϖ ^ k • x`, hence compact.
- `exists_mem_orderLevel_neg`: every `x` lies in some `ϖ ^ (-n) R`, `n : ℕ`, because `ϖ ^ n • x → 0`
  and `R` is a neighbourhood of `0`.
- `exists_orderLevel_subset`: every neighbourhood of `0` contains some `ϖ ^ n R`, `n : ℕ`. Proof:
  by compactness of `R` (`IsCompact.eventually_forall_of_forall_eventually` for
  `(c, y) ↦ c • y`) all `c • y`, `y ∈ R`, lie in the neighbourhood for `c` near `0`; take
  `c = ϖ ^ n`.
- `eq_zero_of_forall_mem_orderLevel` (`[FiniteDimensional F A]`): an element of every `ϖ ^ n R`
  is `0`, since `A` is Hausdorff (`t2Space_of_finiteDimensional`) and the lattices shrink into
  every neighbourhood of `0`.
- `exists_inverse_one_add` (`[FiniteDimensional F A]`): for `u ∈ ϖ R` there is `v ∈ R` with
  `(1 + u) v = 1 = v (1 + u)`. Proof: if `(1 + u) y = 0` then `y = -u y` lies in every
  `ϖ ^ n R`, so `y = 0`; left multiplication by `1 + u` is injective, hence surjective by finite
  dimension, giving `v` with `(1 + u) v = 1` and then `v (1 + u) = 1`. Finally `v = 1 - u v`, so
  an induction on `j` shows `v ∈ ϖ ^ (-j) R → v ∈ R`.

## Provenance

These are the standard properties of lattices in a finite-dimensional vector space over a local
field (André Weil, *Basic Number Theory*, second edition, 1973, source ID
`weil-1973-basic-number-theory`, Chapter II, §2, printed pp. 27–29), specialized to the
multiples of an order. In Harish-Chandra, *Admissible invariant distributions on reductive
p-adic groups* (1999, source ID `harish-chandra-1999-admissible-invariant-distributions`,
Part II, §§11–13, printed pp. 58–69) the same bookkeeping is done with a norm on `g`; the
lattices `ϖ ^ k R` serve as its balls. The statements and proofs are internal to the Library.
