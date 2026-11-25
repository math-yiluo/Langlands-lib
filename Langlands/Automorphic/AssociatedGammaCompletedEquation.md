# From a completed global equation to the comparison-engine format

Supporting module (module `Langlands.Automorphic.AssociatedGammaCompletedEquation`), glue step G1 of the proof of
`AssociatedGammaStatement`. It converts a completed global functional equation into the
three inputs `Admissible`, `HasEulerProductsOutside` and `FunctionalEquation` of the
published finite comparison engine (`Langlands.Global.FunctionalEquationComparison`,
`RelativeWeilEngine`), at the exceptional set `univ.disjSum B`.

## Declarations

- `hasProd_ne_zero_of_summable`: if `HasProd f a`, every `f i ≠ 0`, and `‖f i - 1‖` is
  summable, then `a ≠ 0`. Proof: Mathlib's `tprod_one_add_ne_zero_of_summable` applied to
  `1 + (f i - 1)`, and `HasProd.tprod_eq`.
- `NonzeroMeromorphic.countable_zeros` (in namespace `CompletedEquationAdapter`): a function
  with nonzero germ everywhere vanishes only on a countable set. Proof: by
  `NonzeroMeromorphic.eventually_ne_zero` the zero set is discrete
  (`discreteTopology_subtype_iff`, `Filter.inf_principal_eq_bot`), and every subset of the
  second-countable `ℂ` is Lindelöf (`HereditarilyLindelofSpace.isLindelof`,
  `IsLindelof.countable`).
- `nonzeroMeromorphic_div_archimedean`: for countably many local factors `l v`, each with a
  countable zero set, a meromorphic `Λ` and a nonzero meromorphic `L` nonzero on the half-plane
  `re s > σ`, such that on that half-plane `‖l v s - 1‖` is summable and `Λ s = L s * p` with
  `HasProd (l · s) p`: then `Λ / L` is nonzero meromorphic. Proof: if the order of `Λ / L` at
  `x = σ + 1` were `⊤`, the function would vanish on a punctured neighbourhood of `x` inside the
  half-plane. The union of the zero sets of the local factors with `{x}` is countable, so its
  complement is dense (`Set.Countable.dense_compl`) and meets that neighbourhood at a point `s`.
  There all factors are nonzero, so the product `p` is nonzero by the previous lemma, and
  `Λ s / L s = p ≠ 0`, a contradiction. The order is then finite everywhere since `ℂ` is
  preconnected (`MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected`).
- `functionalEquation_of_completedEquation`: the general conversion. Data: finitely many
  archimedean `LocalFactors` `arch w` (all three functions nonzero meromorphic) with products
  `Linf`, `Ldinf`, `εinf`, where `Linf` and `Ldinf` are nonzero on a right half-plane; countably
  many finite local factors `l v`, `d v`, `e v`, nonzero meromorphic (so with countable zero
  sets), with `l v`, `d v` nonzero on a right half-plane depending on `v`; finite sets
  `S ⊆ B` with `e v = 1` for `v ∈ B \ S`; meromorphic `Λ`, `Λd` that on a right half-plane equal
  `Linf` resp. `Ldinf` times the absolutely convergent Euler products of `l` resp. `d`; and the
  equation `Λ s = (∏_(v ∈ S) e v s) εinf s Λd (1 - s)` on a codiscrete set. Conclusion: for the
  `FiniteEulerData` with local factors `Sum.elim arch (l, d, e)` and partial L-functions
  `Λ · Linf⁻¹ · (∏_(z ∈ B) l z)⁻¹` and `Λd · Ldinf⁻¹ · (∏_(z ∈ B) d z)⁻¹` there is `σ'` with
  `Admissible`, `HasEulerProductsOutside … σ'` and `FunctionalEquation` at `univ.disjSum B`.

## Proof of the conversion

- Admissibility: the partial L-functions are nonzero meromorphic by
  `nonzeroMeromorphic_div_archimedean` and `NonzeroMeromorphic.mul`/`inv`/`finsetProd`; the
  local factors are nonzero meromorphic by hypothesis.
- Euler products: take `σ'` the maximum of the half-plane bounds of the Euler products, of
  `Linf`, `Ldinf`, and of the factors in `B`. There `Λ / Linf` is the full Euler product; the
  published `hasProd_compl_of_ne_zero` removes the nonzero factors in `B`, and
  `complDisjSumEquiv` reindexes the complement of `univ.disjSum B` in `I ⊕ Q` as the
  complement of `B` in `Q`.
- Functional equation: after `Finset.prod_disjSum`, the left side is meromorphically equal to
  `Λ` and the right side to `εinf (∏_(z ∈ B) e z) Λd(1 - ·)` (cancellation off the discrete
  zero sets of the nonzero meromorphic factors, `eventually_ne_zero` and `reflect`); the
  middle equality is the hypothesis with `∏_S e = ∏_B e` (`Finset.prod_subset`), turned into a
  `MeromorphicEq` by `meromorphicEq_of_codiscrete`.

No bound on Satake parameters is used: only the finitely many factors in `B` need to be nonzero
on a half-plane, and the nonvanishing of the germ of the partial L-function comes from the
countable zero sets.
