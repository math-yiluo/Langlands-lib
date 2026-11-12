# Split rank of an affine Weil restriction

Author: Worker 5196.

## Lean meaning

`Langlands.GroupScheme.AffineWeilSplitRankStatement` is a closed
`Prop`-valued definition at an arbitrary universe `u`. It asserts the
following. Let `k K : Type u` be fields with `[Algebra k K]`,
`[FiniteDimensional k K]` and `[Algebra.IsSeparable k K]`. Let `G'` be a
group scheme over `Spec (CommRingCat.of K)` with `IsConnectedReductive G'`.
Then

```text
splitRank (AffineWeil.groupScheme k K G') = splitRank G'
```

in `ℕ∞`. The left side is the split rank over `k` of the published affine
Weil restriction `R_{K/k} G'`, a group scheme over `Spec (CommRingCat.of k)`.
The right side is the split rank of `G'` over `K`.

All objects are published Library objects. `IsConnectedReductive` is in
`Reductive.Basic`, `splitRank` in `Rational.SplitTorus` and
`AffineWeil.groupScheme` in `AffineWeilRestriction`. No new definition is
introduced.

`AffineWeil.groupScheme` needs `[IsAffine G'.X.left]` and
`[LocallyOfFiniteType G'.X.hom]`. Both are obtained inside the statement
from the fields of `IsConnectedReductive G'`:

- `hG'.isAffineHom`, through Mathlib's `isAffine_of_isAffineHom`, gives
  `IsAffine G'.X.left`;
- `hG'.smooth`, through Mathlib's instances, gives `LocallyOfFiniteType`.
  Smooth implies locally of finite presentation, which implies locally of
  finite type.

These instances are proof-irrelevant propositions. Hence no premise or datum
is added beyond those listed above. The construction's `Module.Finite k K`
comes from `FiniteDimensional k K`, and `Module.Projective k K` holds for any
vector space.

This is a statement only; nothing is proved here.

## Source

Armand Borel and Jacques Tits, *Groupes réductifs*, Publ. Math. IHÉS 27
(1965), registered `borel-tits-1965-groupes-reductifs`.

- 6.17, printed p.111 / PDF p.58, fixes the setting used in 6.17–6.21. `K` is
  a separable extension of finite degree `d` of `k`, contained in `k_s`,
  with embeddings `σ_1 = id, …, σ_d` into `k_s`. For a connected `K`-group
  `H`, `H' = R_{K/k} H` comes with `μ : H' → H` such that
  `μ° = (σ_1 μ, …, σ_d μ) : H' → σ_1H × … × σ_dH` is a `k_s`-isomorphism.
- 6.19, printed pp.111–112 / PDF pp.58–59: `R_{K/k}` gives a bijection
  between maximal tori defined over `K` of `H` and maximal tori defined over
  `k` of `H'`.
- 6.20, printed p.112 / PDF p.59: for a torus `T` over `K`, the character
  groups `X*(T)_K` and `X*(R_{K/k} T)_k` are isomorphic. Hence the largest
  split subtori `T_d` and `T'_d` have the same dimension.
- 6.21(i), printed p.112 / PDF p.59: “Supposons maintenant H réductif. De
  6.19, 6.20, on tire : r_K(H) = r_k(H')”. They add that if `A` is a
  maximal `K`-split torus of `H`, then the largest `k`-split subtorus `A'_d`
  of `A' = R_{K/k} A` is a maximal `k`-split torus of `H'`.

The statement is this rank equality with `H = G'` and `H' = R_{K/k} G'`.

## Formulation choices

- **Split rank.** Borel–Tits's `r_k` is the common dimension of the maximal
  `k`-split tori. The Library's `splitRank` is the supremum, in `ℕ∞`, of
  `Nat.card I` over finite `I : Type u` admitting a closed-subgroup
  homomorphism `splitTorus (Spec k) I ⟶ G`. The Lean statement compares the
  Library split ranks on both sides. It does not separately assert that
  they are finite or that they agree with Borel–Tits's `r_k`.
- **Weil restriction.** `R_{K/k}` is the published
  `AffineWeil.groupScheme k K G'`, which carries the original group law. It
  replaces Borel–Tits's restriction of scalars of quasi-projective
  varieties. The published construction is the actual Weil restriction of
  an affine group scheme of finite type. The statement does not assert that
  `AffineWeil.groupScheme k K G'` is reductive.
- **Hypotheses on `G'`.** Borel–Tits assume `H` connected (6.17) and
  reductive (6.21(i)). `IsConnectedReductive G'` is the Library's form of
  this hypothesis: smooth, affine, connected, with trivial geometric
  unipotent radical. It is the only hypothesis on `G'`.
- **The extension.** Both fields lie in `Type u`. Finiteness and
  separability are explicit instance hypotheses, as in 6.17. Borel–Tits's
  normalization `K ⊂ k_s` only chooses an embedding into a separable
  closure, which always exists, so it is not imposed and no embedding is
  chosen. Nothing is asserted for inseparable extensions.
- **Generality.** The characteristic is arbitrary. There is no perfectness,
  infinitude, local-field or topological hypothesis on `k` or `K`.

## Role

The task that publishes this statement exists for the split-rank-one case of
the local Kneser–Tits problem (Prasad–Raghunathan, *On the Kneser–Tits
problem*, 1985, §2, registered `prasad-raghunathan-1985-kneser-tits`). There
an almost-simple simply connected group is written as a Weil restriction
`R_{K/k} G'` with `G'` absolutely almost-simple. This uses the published
`SimplyConnectedAlmostSimpleWeilRestrictionStatement` in
`SimplyConnected.AlmostSimpleWeilRestrictionStatement`. The present
statement transfers the condition on the split rank from `G` to `G'`. Its
companion `AffineWeilParabolicElementarySubgroupStatement` (module
`Rational.AffineWeilParabolicElementaryStatement`) transfers the subgroup
generated by rational parabolic radicals.
