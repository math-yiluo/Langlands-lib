# Normalized compact sections for the strict rank-one extension

`Langlands.RankinSelberg.rankOneExtensionCompactSection` proves exactly the
published `Langlands.RankinSelberg.RankOneExtensionCompactSectionStatement.{uF,uV,uW}`.
The theorem adds no parameters or hypotheses. It covers every prime, canonical
p-adic field, supplied unitary additive character, supplied self-dual Haar
measure, all `t, k` including zero, every quasicharacter `χ`, all smooth `π` and
`σ`, all vectors `v, w`, and every open neighbourhood `O` of zero in
`Fin (t + 1) → F`. The section is an actual element of
`rankOneExtensionLowerSection F t χ σ`, the carrier of the published normalized
lower induction `rankOneExtensionLowerModel`. Its inducing vector is the published
pure tensor `rankOneExtensionLowerPureTensor w (ULift.up 1)` in the reversed
carrier `(W, ULift ℂ)`.

## Route

The proof does not follow the averaging construction of the source (see the end of
this note). It takes the published double-coset section `P̄ · 1 · K` of the lower
induction. Here `P̄` is the lower parabolic of `rankOneExtensionLowerShape t`, with
blocks `(t + 1, 1)`, and `K` is a compact open subgroup with block Iwahori
factorization `K = (K ∩ N̄)(K ∩ M)(K ∩ N)` for that shape. `N` is the upper block
radical, which is exactly the complementary upper cell `u(y) = [I, y; 0, 1]`.
Since `P̄ ∩ N = 1`, the factorization determines the section on the whole upper
cell, not only at one point.

## Group and cell lemmas

- `BlockShape.eq_one_of_mem_oppositeParabolic_of_mem_unipotentSubgroup`: an
  element of `P̄ ∩ N` is the identity. It is proved on the matrix entries in
  block indices: block-lower entries vanish because the element is in `N`,
  block-upper entries vanish because it is in `P̄`, and the diagonal blocks are
  identities because it is in `N`.
- `oppositeUnipotentSubgroup_le_oppositeParabolic` and
  `leviSubgroup_le_oppositeParabolic`: `N̄ ≤ P̄` and `M ≤ P̄`.
- `rankOneExtensionCellCoordinate g` is a proof-local helper definition. It is the
  column `i ↦ g (rankOneExtensionHeadIndex t i) (rankOneExtensionScalarIndex t)`,
  that is, the entries `(i, t + 1)` for `i ≤ t`. The proof shows the following.
  - Reading the coordinates of `u(y)` gives `y`.
  - `u(0) = 1` reuses `rankOneExtensionUpperCell_zero` from
    [RankOneExtensionCellAlgebra](RankOneExtensionCellAlgebra.md);
    the shared cell topology module supplies `u(y)⁻¹ = u(-y)`.
  - `u(y) ∈ N` (`rankOneExtensionUpperCell_mem_unipotentSubgroup`).
  - Every `n ∈ N` equals `u` of its own coordinates
    (`eq_rankOneExtensionUpperCell_of_mem_unipotentSubgroup`).

  The block indices of the lower shape are matched with the published cell
  coordinates by `rankOneExtensionLowerShape_index_zero/one`. The coordinate map is
  continuous because matrix entries are continuous. `u` is continuous into the
  unit group by `Units.continuous_iff`, using the inverse formula `u(-y)`.

## Smoothness of the inducing representation

- `isSmooth_oppositeInducing`: for any block shape and any smooth Levi
  representation, the inducing representation of
  `normalizedOppositeParabolicInduced` is smooth. This representation is the
  inflation along the opposite Levi projection, twisted by
  `oppositeParabolicHalfModulus`. Pulling back along the continuous projection
  (`isSmooth_comp`) preserves smoothness. So does twisting by a character with
  open kernel (`isSmooth_twist_iff`, `isOpen_ker_oppositeParabolicHalfModulus`).
- `rankOneExtensionLowerFamily_isSmooth`: block `0` is `σ` and block `1` is the
  lifted character, which is smooth by `rankOneExtensionCharacter_isSmooth`.
  `FiniteTensor.isSmooth_external` then makes the block tensor smooth.
  `rankOneExtensionLowerInducing_isSmooth` combines the two.

## The construction (`exists_rankOneExtensionCellSection`)

The construction lemma works for an arbitrary smooth representation `ρ` of `P̄` on
any complex module `X`, with any vector `x₀ ∈ X`.

1. **Neighbourhood of 1.** Smoothness gives an open subgroup `Kπ` fixing `v` and an
   open subgroup `H ≤ P̄` fixing `x₀`. Write `H = P̄ ∩ O'` with `O'` open in `G`.
   Then `U = O' ∩ rankInclusion⁻¹(Kπ) ∩ coord⁻¹(O)` is an open neighbourhood of
   `1`, by continuity of `rankInclusion` and of the coordinates, since
   `coord(1) = 0 ∈ O`.
2. **The subgroup.** `exists_compactOpenSubgroup_hasBlockIwahoriFactorization`
   gives a compact open `K ⊆ U` with block Iwahori factorization for the lower
   shape. Bijectivity of the Iwahori product writes every `k ∈ K` as `q n` with
   `q ∈ (K ∩ N̄)(K ∩ M) ⊆ P̄` and `n ∈ K ∩ N`.
3. **Test function and the supplied measure.** Set `L = u⁻¹(K)`.
   - `L` is open and closed, as the preimage of an open subgroup under the
     continuous map `u`, and it contains `0`.
   - `L` is compact: it is a closed subset of the image of `K` under the
     coordinates.
   - Let `μ = rowMeasure ν.val (t + 1)`, the finite product of the supplied Haar
     measure. Then `μ(L) > 0` because `L` is a nonempty open set
     (`IsOpen.measure_pos`), and `μ(L) < ∞` because `L` is compact.
   - Set `φ = μ.real(L)⁻¹ · 1_L`. It is a Schwartz–Bruhat function: locally
     constant as the indicator of a clopen set, with compact support.
   - `supp φ = L`, and `φ` is integrable (`integrableOn_const`,
     `IntegrableOn.integrable_indicator`).
   - `∫ φ dμ = μ.real(L) · μ.real(L)⁻¹ = 1` (`integral_indicator_const`).

   Only the facts that `ν.val` is an additive Haar measure, positive on open sets
   and finite on compact sets, are used. Self-duality is not used.
4. **The section.** `c • x₀`, with `c = μ.real(L)⁻¹`, is fixed by the conjugate
   subgroup `P̄ ∩ K`, because `K ⊆ O'` and hence `P̄ ∩ K ⊆ H`. Set
   `s = Induction.compactDoubleCosetSection P̄ ρ K hK 1 (c • x₀)`.

   Right smoothness is built into this published constructor. It produces an
   element of `Induction.SmoothFunctions` that is left `P̄`-covariant and right
   invariant under the open subgroup `K` (`compactDoubleCosetSection_mul`). It has
   compact support modulo `P̄`, with
   `s(p · 1 · k) = ρ(p)(c • x₀)` (`compactDoubleCosetSection_apply`).
5. **Support.** By `compactDoubleCosetSection_support_subset`, `s(g) ≠ 0` implies
   `g ∈ P̄ k'` for some `k' ∈ K`. Factoring `k'` as in step 2 gives `g = q n` with
   `q ∈ P̄` and `n ∈ K ∩ N`.
6. **Conclusions.**
   - *Restriction to the cell.* If `y ∈ L`, then
     `s(u(y)) = s(1 · 1 · u(y)) = c • x₀ = φ(y) • x₀`. If `y ∉ L` and
     `s(u(y)) ≠ 0`, then `u(y) = q n` as in step 5. So
     `q = u(y) n⁻¹ ∈ P̄ ∩ N = 1`, hence `u(y) = n ∈ K`, contradicting `y ∉ L`.
     So `s(u(y)) = 0 = φ(y) • x₀`.
   - *Support condition.* If `s(g) ≠ 0`, then `g = q n` with `n ∈ K ∩ N`. So
     `n = u(coord n)` and `coord n ∈ L = supp φ`.
   - *Support in `O`.* For `y ∈ L`, `u(y) ∈ K ⊆ coord⁻¹(O)` and `coord(u(y)) = y`.
   - *Fixing `v`.* For `y ∈ L`, `u(y) ∈ K ⊆ rankInclusion⁻¹(Kπ)`, so
     `π(rankInclusion (k + 1) (u(y))) v = v`.

## The final theorem

`rankOneExtensionCompactSection` applies the construction to the inducing
representation of `rankOneExtensionLowerModel F t χ σ`, which is smooth by
`rankOneExtensionLowerInducing_isSmooth`. It takes
`x₀ = rankOneExtensionLowerPureTensor w (ULift.up 1)` and
`f = (rankOneExtensionLowerModel F t χ σ).asModuleEquiv.symm s`.
`rankOneExtensionLowerSectionEval` is by definition `Induction.eval` of the
underlying section, so the six conclusions transfer unchanged.

## Relation to the literature

JPSS (1983), Lemma (5.5), printed pages 424–425 (PDF pages 59–60), formulas
(5)–(7), constructs `f` with `f(u; h) = W₁(h) φ(u)` on `Ū_Q`, `∫ φ = 1` (formula
(5)), and `φ` supported where `W` is invariant (formula (7)). The source obtains
`f` by averaging `F = β ⊗ φ ⊗ W₁` over `Q`. The Lean proof instead takes the
double-coset section over a block-Iwahori compact open subgroup. It replaces the
Whittaker model `W₁` with the published reversed pure tensor `w ⊗ 1`, and the
invariance of `W` with the fixed vector `v` of `π`, as the target statement
specifies.

This proof is an internal derivation from published Library results. Worker 816
wrote it.

The three general block-subgroup lemmas above are imported from [OppositeBlockIntersection](../../Group/GL/OppositeBlockIntersection.md).

The inverse law and continuity of the upper cell are imported from [RankOneExtensionCellTopology](RankOneExtensionCellTopology.md).
