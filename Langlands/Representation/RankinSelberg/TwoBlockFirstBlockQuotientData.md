# The first-block norm-one quotient and the first-block slice average

Module `Langlands.Representation.RankinSelberg.TwoBlockFirstBlockQuotientData`,
namespace `Langlands.RankinSelberg.TwoBlockFirstBlockQuotient`.

Author: Worker 823.

This module is a definitions unit. It builds the subgroups, quotients and
averages that appear in the second disintegration of JPSS (1983),
Section (4.6), equation (6). These are internal data for that displayed
formula, not a numbered theorem of the original. The module does not state or
prove equation (6).

## Source and conventions

Source: Jacquet, Piatetski-Shapiro and Shalika, *Rankin–Selberg convolutions*
(1983), source ID `jpss-1983-rankin-selberg`, Section (4.6), printed pages
411–413. The zero-based PDF index is the printed page minus 366. No errata note
for this source exists in the project literature.

On printed page 412, after rewriting `Ψ^m` as an integral over
`N_(t_1,t_2) \ G_r^m`, the source disintegrates through the first-block general
linear group. With `r = t_1 + t_2`, equation (6) reads

```text
∫_{N_(t_1,t_2) \ G_r^m} f(g) dg
  = ∫_{G_(t_1)^0 N_(t_1,t_2) \ G_r^0} dh ∫_{N_(t_1) \ G_(t_1)^m} f[diag(a, 1) h] d^×a.
```

Here `G_n^m = {g ∈ G_n : |det g| = q^(-m)}` (Section 4.2, printed page 406),
`G_(t_1)` sits in `G_r` as `a ↦ diag(a, 1_(t_2))`, and `N_(t_1,t_2)` is the
group of matrices `diag(n_1, n_2)` with `n_i ∈ N_(t_i)` (display (5)).

In the table, the source's slice index `m` is written `k` and its outer variable
`h` is written `g`, because `m` and `h` already name the block ranks and the
rank hypothesis here.

| JPSS | Here |
| --- | --- |
| block ranks `t_1`, `t_2` | `a = m 0 + 1`, `b = m 1 + 1` |
| rank `r = t_1 + t_2` | `t + 1`, with `h : ∑ i, (m i + 1) = t + 1` |
| block shape | `succBlockShape m h` |
| `G_r` | `G = GeneralLinear (t + 1) F.Carrier` |
| `N_(t_1,t_2)` | `H = TwoBlockUnipotentQuotient.blockUnipotent h F.Carrier` |
| `N_(t_1,t_2) \ G_r^m` | `TwoBlockUnipotentQuotient.determinantSlice F h k` |
| `a ↦ diag(a, 1)` | `firstBlockEmbedding h F.Carrier` |
| `G_(t_1)^0` | `normOneSubgroup F (m 0 + 1)` |
| `G_(t_1)^0 N_(t_1,t_2)` | `L = mixedSubgroup F h` |
| `G_(t_1)^0 N_(t_1,t_2) \ G_r^0` | `determinantSlice F h 0` in `MixedQuotient F h` |
| `N_(t_1) \ G_(t_1)^m` | `RankinSelberg.determinantSlice T (m 0) k` |
| inner integral at the outer point `g` | `fiberIntegral F h μA k f g` |
| outer integrand, as a function on `L \ G` | `firstBlockAverage F h μA hμA k f` |

Throughout, `p` is a prime, `F : PadicField.{uF} p` is a canonical `p`-adic
field, `T = F.canonicalTopologicalData`, `t : ℕ` and `m : Fin 2 → ℕ` are
arbitrary, and `h : ∑ i, (m i + 1) = t + 1`. Both block ranks are positive and
every positive value is included, among them `a = 1` and `b = 1`. Topologies are
the canonical `p`-adic ones, with the induced matrix, subtype, product and
quotient topologies. The order of an element is the published normalized order
`T.ord`. The module has no representation, character or Whittaker hypotheses.

**Why `L = diag(GL_a^0, N_b)`.** The source's group `G_(t_1)^0 N_(t_1,t_2)`
consists of the products `diag(u, 1) diag(n_1, n_2) = diag(u n_1, n_2)` with
`|det u| = 1` and `n_i` upper unipotent. Since `|det n_1| = 1`, the first block
of `N_(t_1,t_2)` is absorbed by `GL_a^0`. The group is therefore
`diag(GL_a^0, N_b)`, and the module defines `L` directly as the image of
`(u, n) ↦ diag(u, n)`. The inclusion `H ≤ L` is proved separately below.

**Outer and inner domains.** The outer domain of (6) is the zero
determinant-order slice of `L \ G`, here `determinantSlice F h 0`. It is not all
of `MixedQuotient F h`, and the module does not identify the two. The inner
domain `N_(t_1) \ G_(t_1)^m` is the published slice
`RankinSelberg.determinantSlice T (m 0) k` of the published small quotient
`RankinSelberg.LeftUnipotentQuotient (m 0) F.Carrier = N_a \ GL_a`.

## Algebra of block-diagonal matrices (sections `Algebra`, `TwoBlocks`)

These hold over any commutative ring `R`.

- The reused `Langlands.Parabolic.FlattenedModulusCalculation.determinant_leviEmbedding`
  states `determinant (B.leviEmbedding R L) = ∏ i, determinant (L i)` for any
  `B : BlockShape n` and `L : B.Levi R`. Its proof uses Mathlib's determinant of a
  block-triangular matrix; see
  [FlattenedRefinementModulusCalculation](../Parabolic/FlattenedRefinementModulusCalculation.md).
- `blockPair R : GeneralLinear (m 0 + 1) R × GeneralLinear (m 1 + 1) R →*
  ∀ i : Fin 2, GeneralLinear (m i + 1) R`, the Levi element with blocks
  `(u, w)`, defined as `Pi.mulSingle 0 u * Pi.mulSingle 1 w`. The lemmas are
  `blockPair_apply_zero`, `blockPair_apply_one`, and
  `blockPair_eta : blockPair R (L 0, L 1) = L`.
- `determinant_leviEmbedding_blockPair`: `det diag(u, w) = det u * det w`.
- `leviEmbedding_blockPair_mem_blockUnipotent`: if `u` and `w` are upper
  unipotent, then `diag(u, w) ∈ H`.
- `mem_parabolic_of_index_one_zero`: a matrix whose lower-left block vanishes
  lies in the published parabolic `(succBlockShape m h).parabolic R`.
- `leviEmbedding_leviProjection_of_blocks`: a matrix whose two off-diagonal
  blocks vanish is the Levi embedding of its published Levi projection.
- `det_firstBlock_eq`: if both off-diagonal blocks vanish and the second
  diagonal block is upper unipotent, then the determinant of the first diagonal
  block, a submatrix, equals `det g`.

## The first-block embedding (contract item 1)

- `firstBlockEmbedding h R : GeneralLinear (m 0 + 1) R →* GeneralLinear (t + 1) R`
  is `u ↦ diag(u, 1_b)`. It is the published Levi embedding
  `(succBlockShape m h).leviEmbedding R` composed with `u ↦ blockPair R (u, 1)`.
  `firstBlockEmbedding_apply` is the representative formula
  `firstBlockEmbedding h R u = (succBlockShape m h).leviEmbedding R (blockPair R (u, 1))`.
- The four block-entry formulas, indexed by the published `B.index`:
  `firstBlockEmbedding_index_zero_zero` (entry `u a b`),
  `firstBlockEmbedding_index_zero_one` and `firstBlockEmbedding_index_one_zero`
  (entry `0`), and `firstBlockEmbedding_index_one_one`
  (entry `if a = b then 1 else 0`).
- `firstBlockEmbedding_injective`: injectivity.
- `determinant_firstBlockEmbedding`: `det (firstBlockEmbedding h R u) = det u`.
- `firstBlockEmbedding_mem_blockUnipotent`: if `u` is upper unipotent, then
  `firstBlockEmbedding h R u ∈ H`.
- `firstBlockEmbedding_mul_leviEmbedding_blockPair`: the block identity
  `diag(v, 1) diag(u, w) = diag(1, w) diag(v u, 1)`.
- `continuous_firstBlockEmbedding`: continuity for any topology on the
  commutative ring `R`. It uses `continuous_blockPair` and the published continuous Levi
  embedding.
- Over a field `K`: `last_eq_index_one` says that the last coordinate
  `Fin.last t` is the last index of the second block (because `b ≥ 1`), and
  `lastRow_firstBlockEmbedding_mul` says that
  `lastRow (firstBlockEmbedding h K u * g) = lastRow g` for every `u` and `g`.
  Here `lastRow` is the published `RankinSelberg.lastRow`.

## The norm-one block and the mixed subgroup `L` (contract item 2)

- `normOneSubgroup F n : Subgroup (GeneralLinear n F.Carrier)` is an
  abbreviation for `(F.canonicalTopologicalData.determinantNorm n).ker`. For
  `n = a` this is the contract's `A0 = GL_a^0`. `mem_normOneSubgroup_iff`
  unfolds it. `mem_normOneSubgroup_iff_normalizedAbs` says that membership is
  `T.normalizedAbs (det u) = 1`. `ord_determinant_eq_zero` says that a norm-one
  matrix has `T.ord (det u) = 0`.
- `mixedEmbedding F h : normOneSubgroup F (m 0 + 1) × upperUnipotent (m 1 + 1) F.Carrier →* G`
  is `(u, n) ↦ diag(u, n)`, again through the published Levi embedding.
  The lemmas are `mixedEmbedding_apply` (representative formula), the four
  block-entry lemmas `mixedEmbedding_index_zero_zero` (entry `u a b`),
  `mixedEmbedding_index_zero_one`, `mixedEmbedding_index_one_zero` (entry `0`)
  and `mixedEmbedding_index_one_one` (entry `n a b`), `mixedEmbedding_injective`,
  and `determinant_mixedEmbedding : det (mixedEmbedding F h x) = det x.1`.
- `mixedSubgroup F h : Subgroup G` is `L`, defined as the actual image
  `(mixedEmbedding F h).range`. `mixedEmbedding_mem` is the image membership.
- Intrinsic block-entry characterization. `mem_mixedSubgroup_iff` says that
  `g ∈ L` exactly when the following hold:
  - both off-diagonal blocks of `g` vanish;
  - the first diagonal block (the submatrix on `B.index 0`) has determinant of
    normalized absolute value `1`; such a block is invertible, see
    `det_firstBlock_ne_zero`;
  - the second diagonal block is upper unipotent: its entries below the
    diagonal vanish and its diagonal entries are `1`.

  `mem_mixedSubgroup_iff_determinantNorm` is the equivalent form in which the
  first-block condition is replaced by `g ∈ normOneSubgroup F (t + 1)`. The
  replacement uses `det_firstBlock_eq`. This form is used for closedness.
- `mixedSubgroup_le_normOneSubgroup : L ≤ (T.determinantNorm (t + 1)).ker`.
- `blockUnipotent_le_mixedSubgroup : H ≤ L`. The first block of an element of
  `H` is upper unipotent and hence has norm one, by the published
  `determinantNorm_eq_one_of_mem_upperUnipotent`.
- `mixedSubgroup_le_parabolic : L ≤ (succBlockShape m h).parabolic F.Carrier`.
- `mixedCoordinates F h : mixedSubgroup F h → normOneSubgroup F (m 0 + 1) × upperUnipotent (m 1 + 1) F.Carrier`
  extracts the two diagonal blocks with the published Levi projection. The
  inverse laws are `mixedCoordinates_mixedEmbedding` and
  `mixedEmbedding_mixedCoordinates`.
- `mixedSubgroupEquiv F h : normOneSubgroup F (m 0 + 1) × upperUnipotent (m 1 + 1) F.Carrier ≃* mixedSubgroup F h`
  is the multiplicative equivalence. Its forward map is `mixedEmbedding`
  (`mixedSubgroupEquiv_apply_val`). Its inverse has entries
  `g (B.index i a) (B.index i b)` (`mixedSubgroupEquiv_symm_apply_fst`,
  `mixedSubgroupEquiv_symm_apply_snd`).
- `mixedSubgroupHomeomorph F h`, of the same type with `≃ₜ*`, is the same
  equivalence as a `ContinuousMulEquiv` for the canonical topology
  (`mixedSubgroupHomeomorph_toMulEquiv`). The forward map is continuous by the
  published continuous Levi embedding. The inverse is continuous by the
  published continuous Levi projection.
- `isClosed_mixedSubgroup`: `L` is closed in `G`. By
  `mem_mixedSubgroup_iff_determinantNorm`, `L` is an intersection of
  closed sets: the conditions that single entries take fixed values (closed
  because each entry map is continuous and `F.Carrier` is Hausdorff), and the
  kernel of `T.determinantNorm (t + 1)`. That kernel is open
  (`T.isOpen_ker_determinantNorm`) and hence closed, being an open subgroup. The
  proof does not use any statement that a continuous image of a closed set is
  closed.

## The mixed quotient `L \ G` (contract item 3)

- `MixedQuotient F h` is an abbreviation for
  `QuotientIntegration.LeftQuotient (mixedSubgroup F h)`, with its quotient
  topology.
- `projection F h : TwoBlockUnipotentQuotient.BlockQuotient h F.Carrier → MixedQuotient F h`
  is `[g]_H ↦ [g]_L`. It is defined by `QuotientIntegration.descend`, which
  applies because `H ≤ L`. The lemmas are `projection_mk` (representative
  formula), `projection_surjective`, `continuous_projection`, and
  `projection_rightTranslate` (compatibility with the published right
  translations).
- `t2Space_mixedQuotient`: `L \ G` is Hausdorff, by the published
  `leftQuotient_t2Space` and `isClosed_mixedSubgroup`.
- `determinantOrder F h : MixedQuotient F h → ℤ` is the descent of
  `g ↦ T.ord (det g)`. It is well defined because every element of `L` has norm
  one, so its determinant has order `0`. The lemmas are `determinantOrder_mk`
  (representative evaluation), `continuous_determinantOrder` (into the discrete
  integers), and `determinantOrder_projection_mk`.
- `determinantSlice F h k = {q | determinantOrder F h q = k}`, with
  `mem_determinantSlice`, `mk_mem_determinantSlice`,
  `isClopen_determinantSlice`, and `measurableSet_determinantSlice` (for every
  Borel structure on `L \ G`).
- `projection_preimage_determinantSlice`: the preimage under `projection` of
  `determinantSlice F h k` is the published slice
  `TwoBlockUnipotentQuotient.determinantSlice F h k` of `H \ G`.
- `determinantOrder_rightTranslate`: right translation by `g` adds
  `T.ord (det g)` to the determinant order.
  `rightTranslate_mem_determinantSlice` gives the corresponding shift:
  `q · g` lies in slice `k` exactly when `q` lies in slice
  `k - T.ord (det g)`.

## The fiber map from the small quotient (contract item 4)

- `fiberPoint h K q g : TwoBlockUnipotentQuotient.BlockQuotient h K`, for
  `q : RankinSelberg.LeftUnipotentQuotient (m 0) K` and `g : GeneralLinear (t + 1) K`
  over a field `K`, is the descent of `u ↦ [firstBlockEmbedding h K u * g]_H`
  along `GL_a → N_a \ GL_a`. It is well defined because for `n ∈ N_a`,
  `diag(n u, 1) g = diag(n, 1) (diag(u, 1) g)` and `diag(n, 1) ∈ H`.
  `fiberPoint_mk` is the representative formula
  `fiberPoint h K [u] g = [firstBlockEmbedding h K u * g]_H`.
- `continuous_fiberPoint`: `(q, g) ↦ fiberPoint q g` is jointly continuous for
  the canonical topology. The proof lifts along
  `N_a \ GL_a × G`. The map `GL_a × G → N_a \ GL_a × G` is an open quotient map
  (by the published `leftQuotient_isOpenQuotientMap` and
  `IsOpenQuotientMap.prodMap`), so continuity can be checked on
  representatives.
- `fiberPoint_mul`: `fiberPoint q (g g') = rightTranslate g' (fiberPoint q g)`.
- `fiberPoint_mem_determinantSlice_iff`:
  `fiberPoint q g ∈ TwoBlockUnipotentQuotient.determinantSlice F h k` exactly
  when `RankinSelberg.determinantOrder T (m 0) q + T.ord (det g) = k`. This
  follows from `det diag(u, 1) = det u`.
- `fiberPoint_mixedEmbedding_mul`: the change-of-fiber identity
  `fiberPoint q (mixedEmbedding F h (u, n) * g) = fiberPoint (rightTranslate u.val q) g`
  for `u` of norm one and `n ∈ N_b`. The proof uses the block identity
  `diag(v, 1) diag(u, n) = diag(1, n) diag(v u, 1)` with `diag(1, n) ∈ H`. This
  is right multiplication of the small quotient by `u`, not left
  multiplication. It is a pointwise identity of fiber maps and is not a
  statement about a measure tower.

## The inner slice integral and the first-block average (contract item 5)

The small quotient `N_a \ GL_a` carries the Borel structure of its quotient
topology, `borel (RankinSelberg.LeftUnipotentQuotient (m 0) F.Carrier)`.

- `NormOneRightInvariant F n μA : Prop` says that for every
  `u : normOneSubgroup F (n + 1)`, right translation by `u` on
  `RankinSelberg.LeftUnipotentQuotient n F.Carrier` is measure preserving for
  `μA`.
- `normOneRightInvariant_of_isCompatible`: for any Borel measurable structures
  on `GL_(n+1)` and `N_(n+1)`, measures `μG` on `GL_(n+1)` and `μH` on
  `N_(n+1)` with `μH` right invariant, and a measure `ν` on the small quotient
  with its Borel structure, the published
  `QuotientIntegration.IsCompatible (upperUnipotent (n + 1) F.Carrier) μG μH ν`
  implies `NormOneRightInvariant F n ν`. This is the field
  `IsCompatible.right_invariant` restricted to norm-one matrices.
- `fiberIntegral F h μA k f g : ℂ`, for a measure `μA` on the small quotient,
  an integer `k`, `f : TwoBlockUnipotentQuotient.BlockQuotient h F.Carrier → ℂ`
  and `g : G`, is the total Bochner integral
  `∫ q in RankinSelberg.determinantSlice T (m 0) k, f (fiberPoint h F.Carrier q g) ∂μA`
  (`fiberIntegral_def`). Its value is `0` when the integrand is not
  integrable.
- `fiberIntegral_mixedEmbedding_mul` and `fiberIntegral_mixedSubgroup_mul`:
  under `hμA : NormOneRightInvariant F (m 0) μA`, the integral is left
  `L`-invariant: `fiberIntegral μA k f (l g) = fiberIntegral μA k f g` for
  `l ∈ L`. By `fiberPoint_mixedEmbedding_mul`, the left side is the integral of
  `q ↦ f (fiberPoint q g)` composed with right translation by `u`. That
  translation preserves `μA` by `hμA`. It also maps the small slice onto itself,
  because `T.ord (det u) = 0` and by the published
  `RankinSelberg.rightTranslate_mem_determinantSlice`. The translation is a
  homeomorphism, hence a measurable embedding, so Mathlib's
  `MeasurePreserving.setIntegral_preimage_emb` applies. No integrability
  hypothesis is needed, since this lemma holds for every integrand.
- `fiberIntegral_mul`: right translation of the base point,
  `fiberIntegral μA k f (g g') = fiberIntegral μA k (f ∘ rightTranslate g') g`.
- `firstBlockAverage F h μA hμA k f : MixedQuotient F h → ℂ` is
  `QuotientIntegration.descend` of `fiberIntegral F h μA k f` along the left
  `L`-invariance above. No coset representative is chosen.
  `firstBlockAverage_mk` gives the representative evaluation
  `firstBlockAverage μA hμA k f [g]_L = ∫ q in N_a \ GL_a^k, f (fiberPoint q g) dμA`.
  `firstBlockAverage_rightTranslate` gives
  `firstBlockAverage μA hμA k f (q · g) = firstBlockAverage μA hμA k (f ∘ rightTranslate g) q`.

In the notation of (6), with the source's slice index `m` written `k`, the inner
integral at an outer point `g ∈ G_r^0` is `fiberIntegral F h μA k f g`. The
outer integrand is `firstBlockAverage F h μA hμA k f` restricted to the slice
`determinantSlice F h 0`. Here `f` is a function on `H \ G`, and `μA` is any
supplied measure that satisfies the hypothesis. The source's `d^×a` corresponds
to a choice of `μA`; the module selects no such measure.

## What is not asserted

This module asserts none of the following:

- equation (6) itself, i.e. the identity
  `∫_{H \ G^k} f = ∫_{L \ G^0} firstBlockAverage μA k f`, either as a
  conclusion or as a hypothesis;
- existence, compatibility or normalization of a quotient measure on `L \ G`,
  `H \ G` or `N_a \ GL_a`, or any quotient-measure identity;
- measurability of `fiberIntegral` or `firstBlockAverage` for arbitrary `f`,
  integrability, absolute convergence, Tonelli or Fubini;
- an identification of the outer slice `L \ G^0` with all of `L \ G`.

It chooses no uniformizer, Haar normalization or substitute quotient. It
contains no first-block functional equation, Section 9.3 lower-block chart,
representation or factor statement.
