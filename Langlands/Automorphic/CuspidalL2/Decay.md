# Rapid decay of cuspidal families along a maximal block

Provenance: internal. This module formalizes a form of the classical fact that cusp
forms decay rapidly in the cusps, along one maximal block parabolic at a time, by an
elementary route: no Fourier expansion is used. The decay is gained one factor `e^{-ℓ}` at a time from the
vanishing constant term (in the mean-value form `hcusp`) together with the mean value
inequality of `Langlands.Automorphic.CuspidalL2.UnipotentMeanValue`. The main theorem
is stated for an abstract family of functions with explicit hypotheses; the
hypotheses are discharged for actual cuspidal operator realizations in a later module.

## Matrix helpers

- `GeneralLinear.blockUnipotent_val_sub_one`: `u(X) - 1` is the reindexed block matrix
  `fromBlocks 0 X 0 0`; `GeneralLinear.blockNilpotent_mul_self`: that matrix squares to `0`.
- `ringEquiv_mixedSpace_infiniteRealEmbedding`: under the Library's identification
  `InfiniteAdeleRing.ringEquiv_mixedSpace` of the infinite adeles with the mixed space,
  `PositiveRealIdeles.infiniteRealEmbedding K s` corresponds to the real scalar `s`
  (`algebraMap ℝ`).
- `ArchimedeanGL.conjNilpotent h g Y`: the archimedean matrix
  `coords (g⁻¹ u(Y) g) - 1`. `conjNilpotent_eq` writes it as
  `coords(g)⁻¹ · N(Y) · coords(g)` with `N(Y) = u(Y) - 1` in coordinates;
  `conjNilpotent_mul_self`: it squares to `0`; `squareZeroElement_eq_conj`: the
  element `1 + conjNilpotent h g Y` is `g⁻¹ u(Y) g`; `conjNilpotent_smul`: scaling `Y` by
  `infiniteRealEmbedding s` scales `conjNilpotent` by `s`; `continuous_conjNilpotent`:
  joint continuity in `(g, Y)`.
- `ArchimedeanGL.lieBasis K n`: a fixed real basis (`Module.finBasis`) of the
  archimedean matrix algebra, and `lieDirection K n k` the corresponding real Lie
  algebra elements. `smoothDifferential_val_eq_sum`: the derivative in direction
  `Zm` equals `∑ k, (lieBasis.repr Zm k) * (derivative in direction lieDirection k)`,
  by linearity of `smoothDifferential` in the direction.
- `scaledBlockSet K D`: block matrices with every entry of the form
  `infiniteRealEmbedding t * z`, `t ∈ [0, 1]`, `z ∈ D`; `isCompact_scaledBlockSet`
  (compact when `D` is) and `mem_scaledBlockSet`.

## Main theorem

`blockDecay_of_cuspidal h φ der hrat L hL hlevel hslice hcusp F₀ w hgrowth N i Q hQ hQF`.
Fix a block decomposition `h : a + b = n`, write `e = finSumFinEquiv.trans (finCongr h)`,
and let `φ : ι → AdelicGL K n → ℂ` be a family with maps `der k : ι → ι` (one per basis
direction `k`) such that:

- `hrat`: each `φ i` is left invariant under rational points;
- `hlevel`: each `φ i` is right invariant under `ofFinite ℓ` for `ℓ` in one open
  subgroup `L` of the finite adelic group;
- `hslice`: for every `i` and finite adelic `y`, the slice
  `g ↦ φ i (ofInfinite g * ofFinite y)` is (the value of) a smooth function whose
  derivative in direction `lieDirection k` is the slice of `φ (der k i)`;
- `hcusp`: if `‖φ i (u(Y) g) - φ i g‖ ≤ M` for every adelic block `Y`, then
  `‖φ i g‖ ≤ M` (for a cusp form this follows from the vanishing of the constant term
  along the block, which is the average of `φ i (u(Y) g)` over the compact quotient of
  block matrices);
- `hgrowth`: for every `i` and compact `Q` whose finite parts lie in `F₀`, there is a
  `C` with `‖φ i (ofInfinite (torInf x) * q)‖ ≤ C * w x` for all `x` and `q ∈ Q`.

Conclusion: for every `N`, `i` and compact `Q` with finite parts in `F₀` there is a `C`
such that whenever `0 ≤ ℓ` and every across-the-block gap satisfies
`x (e (inr r)) - x (e (inl p)) ≤ -ℓ`, then for all `q ∈ Q`,
`‖φ i (ofInfinite (torInf x) * q)‖ ≤ C * exp (-(N ℓ)) * w x`.

The set `F₀` is there because in applications the growth bound `w` is only known
uniformly on finitely many finite-adelic cosets; it is preserved by the construction
below because the enlarged compact set `Q'` has the same finite parts as `Q`.

## Proof

Induction on `N`, for all `i` and `Q` simultaneously. `N = 0` is `hgrowth`.

For `N + 1`, apply finite absorption (`exists_nsmul_conj_blockUnipotent_mem`) to `L`
and the finite parts of `Q`, giving `δ`. Let `D = δ · archimedeanFundamentalSet K`,
`𝒲 = scaledBlockSet K D` (compact) and `Q' = {ofInfinite (u(W)) q : W ∈ 𝒲, q ∈ Q}`
(compact, same finite parts). The induction hypothesis for every `der k i` and `Q'`
gives constants `C k`; compactness of `𝒲 × Q` bounds
`∑ k |lieBasis.coord k (conjNilpotent (infinite q) W)|` by some `B`. The new constant is
`B * ∑ k, C k`.

Given `x`, `ℓ`, `q`, it suffices by `hcusp` to bound
`‖φ i (u(Y) g) - φ i g‖` uniformly in `Y`, where `g = ofInfinite (torInf x) * q`.
Decompose `Y = ξ + δ W` (`exists_matrix_decomposition`). The rational part is removed by
`hrat`; `u(δ W)` splits into its infinite part `u(W_∞)` and its finite part `u(W_f)`
(`AdelicGL.blockUnipotent_eq`); after moving the finite part past `q` it becomes
`q_f⁻¹ u(W_f) q_f ∈ L` and is removed by `hlevel`. Commuting `u(W_∞)` past the torus
(`torInf_inv_mul_blockUnipotent_mul`) gives `u(Y')` with entries
`exp (x_{e(inr r)} - x_{e(inl p)}) * W_∞ p r`, so `Y' = e^{-ℓ} Y''` with `Y'' ∈ 𝒲` by the
gap hypothesis. With `X0 = torInf x * q_∞` and `Zm = conjNilpotent q_∞ Y'`
(square zero), the difference becomes `s0(X0 (1 + Zm)) - s0(X0)` for the slice `s0` of
`φ i` at `q_f`. By the mean value estimate it is bounded by a bound for the derivative
along `X0 (1 + s Zm) = torInf x * u(s Y') * q_∞`, `s ∈ [0, 1]`. Expanding the derivative in
the basis (`smoothDifferential_val_eq_sum`), each term is the slice of `φ (der k i)` at
`ofInfinite (torInf x) * (ofInfinite (u(s Y')) * q)`, whose second factor lies in `Q'`
since `s Y' ∈ 𝒲`; so it is at most `C k * exp (-(N ℓ)) * w x`. The coefficients
satisfy `∑ k |repr Zm k| ≤ e^{-ℓ} B` since `Zm = e^{-ℓ} conjNilpotent q_∞ Y''`
(`conjNilpotent_smul`). Multiplying gives the bound `B (∑ C k) e^{-(N+1) ℓ} w x`.

The rational block-unipotent transport in this argument reuses
`Langlands.Automorphic.rational_blockUnipotent` from `ConstantTerm`.
