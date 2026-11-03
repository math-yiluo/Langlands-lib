# The open-cell integration formula and `γ(P)` (Waldspurger I.1 (2), second formula)

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.OpenCellIntegration`,
namespace `Langlands.HarishChandraSchwartz`. It imports only Mathlib
(`MeasureTheory.Measure.Haar.Unique`, `MeasureTheory.Measure.Prod`); the uniqueness theorem
used is Mathlib's `MeasureTheory.Measure.isMulLeftInvariant_eq_smul`.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082. I.1, printed p. 240 (PDF p. 6): every closed algebraic subgroup
`H` carries the left invariant measure with `mes(H ∩ K) = 1`; for `P = M U` semi-standard,
`G = P K`, `g = u_P(g) m_P(g) k_P(g)`, and for `f ∈ C_c^∞(G)` the second formula of (2) is

`∫_G f(g) dg = γ(P)^{-1} ∫_{U × M × Ū} f(u m ū) δ_P(m)^{-1} dū dm du`, with
`γ(P) = ∫_Ū δ_P(m_P(ū)) dū`.

Waldspurger states (2) without proof; he proves Remark (3) (`γ(P)` depends only on `M`) on
pp. 240–241, which is not treated here. In terms of the left Haar measure
`d_l p = δ_P(m)^{-1} du dm` of `P` (the first formula of (2)), the second formula reads
`∫_G f = γ(P)^{-1} ∫_P ∫_Ū f(p ū) dū d_l p`.

## Scope: abstract data and explicit hypotheses

`G` is a topological group with its Borel σ-algebra; `P` and `V` are subgroups (for
Waldspurger, `P` and `V = Ū`) that are locally compact and second countable for the
subspace topology (instance hypotheses). The measures are a Haar measure `μ` on `G` that is
also right invariant (`[IsHaarMeasure μ] [μ.IsMulRightInvariant]`; for Waldspurger's
unimodular `G` this holds), and Haar measures `μ_P` on `P` and `μ_V` on `V`; no normalization
is assumed in the first results. The coordinates are `openCellMap (p, v) = p v^{-1}`, so the
image is the open cell `P V = P Ū`. Further hypotheses:

- `hι`: `openCellMap` is an open embedding of `P × V` into `G` (for Waldspurger: the
  multiplication `P × Ū → G` is a homeomorphism onto the open cell);
- `hnull`: the complement of the open cell is `μ`-null;
- for the constant: a measurable subgroup `K` with `0 < μ(K) < ∞` (`hK`, `hK0`, `hKtop`;
  Waldspurger's `μ(K) = 1`);
- for the value of the constant, in `openCellConstant_eq_lintegral`: measurable
  multiplication on `P`; a function `d : P → ℝ≥0∞` with `μ_P(S p_0^{-1}) = d(p_0) μ_P(S)`,
  stated as `μ_P((· p_0)^{-1} S) = d(p_0) μ_P(S)` for measurable `S` (`hd`; for Waldspurger
  `d(p_0) = δ_P(m_P(p_0))`); `P ∩ K` measurable in `P` with `μ_P(P ∩ K) = 1` (`hPK`, `hPK1`;
  Waldspurger's normalization); and `ℓ : V → P` with `ℓ(v)^{-1} v^{-1} ∈ K`, the
  `P`-component of `v^{-1}` in `G = P K` (`hℓ`).

None of these hypotheses is proved here for Waldspurger's group.

## Definitions

- `openCellMap (p, v) = p v^{-1}`.
- `openCellConstant μP μV K = ∫_V ∫_P 1_K(p v^{-1}) dμ_P(p) dμ_V(v)`, that is
  `∫_V μ_P{p | p v^{-1} ∈ K} dμ_V(v)` (Waldspurger's `γ(P)`, see below).

## Results

- `openCellMap_mul`: `openCellMap(q x) = q_1 · openCellMap(x) · q_2^{-1}`.
- `image_preimage_mul_openCellMap`: the image of a left translate `q^{-1} S` is the preimage
  of the image of `S` under `g ↦ q_1 g q_2^{-1}`.
- `exists_lintegral_range_openCellMap` (under `hι`): there is `c > 0` with
  `∫_{P V} F dμ = c ∫_P ∫_V F(p v^{-1}) dμ_V dμ_P` for every measurable `F ≥ 0`.
- `exists_lintegral_openCellMap` (under `hι`, `hnull`): the same with `∫_G F dμ` on the left.
- `measure_eq_mul_openCellConstant`: if `∫_G F dμ = c ∫_P ∫_V F(p v^{-1})` for all measurable
  `F ≥ 0` and `K` is a measurable subgroup, then `μ(K) = c · openCellConstant μP μV K`.
- `lintegral_eq_openCellConstant_inv_mul` (I.1 (2), second formula; under `hι`, `hnull`,
  `hK`, `hK0`, `hKtop`): `γ = openCellConstant μP μV K` satisfies `0 < γ < ∞`, and
  `∫_G F dμ = μ(K) γ^{-1} ∫_P ∫_V F(p v^{-1}) dμ_V dμ_P` for every measurable `F ≥ 0`.
- `openCellConstant_eq_lintegral` (under `hd`, `hPK`, `hPK1`, `hℓ`):
  `openCellConstant μP μV K = ∫_V d(ℓ(v)) dμ_V(v)`. For Waldspurger's data, with
  `ū = v^{-1}`, `ℓ(v) = u_P(ū) m_P(ū)`, `d = δ_P ∘ m_P` and an inversion invariant `dū`, this is
  `γ(P) = ∫_Ū δ_P(m_P(ū)) dū`; together with the previous result it gives the finiteness and
  positivity of `γ(P)`.

## Proof notes

The pull-back `ν` of `μ` by the open embedding is a measure on the group `P × V`. A left
translation by `q = (p, v)` corresponds to `g ↦ p g v^{-1}` on the open cell
(`image_preimage_mul_openCellMap`), which preserves `μ` because `μ` is left and right
invariant, so `ν` is left invariant; it is finite on compact sets because compact sets map to
compact sets. By uniqueness of Haar measure on the second countable locally compact group
`P × V`, `ν = c (μ_P × μ_V)`, and Tonelli gives the iterated integral. The constant is
nonzero because the open cell is a nonempty open set. Applied to the indicator of `K`, the
formula gives `μ(K) = c γ` after exchanging the integrals. For the value of `γ`,
`p v^{-1} ∈ K` if and only if `p ℓ(v) ∈ K`, so the inner integral is
`μ_P((· ℓ(v))^{-1}(P ∩ K)) = d(ℓ(v)) μ_P(P ∩ K) = d(ℓ(v))`.

## Open obligations

For Waldspurger's data: that the multiplication `P × Ū → G` is a homeomorphism onto an open
set with null complement; the Haar measures with the normalization `mes(H ∩ K) = 1` and the
unimodularity of `G`; the right translation law of `d_l p` with `d = δ_P ∘ m_P` (which
follows from the first formula of (2), proved generically in `IwasawaIntegration`, and the
modulus relation); the inversion invariance of `dū`; the passage to Waldspurger's coordinates
`(u, m, ū)`; and Remark (3), the independence of `γ(P)` from `U`, are not proved here.
