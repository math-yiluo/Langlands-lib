# The Haar measure `dm du` of `P = M U` and the open-cell formula in coordinates

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.ParabolicHaar`, namespace
`Langlands.HarishChandraSchwartz`. It imports the published modules `IwasawaIntegration`
(`leviUnipotentMul`, `leviUnipotentShift`, `leviUnipotentMul_shift`,
`continuous_leviUnipotentMul`, `measurePreserving_leviUnipotentShift`; through it
`conjUnipotent`, `continuous_conjUnipotent`, `IsConjModulus` and
`IsConjModulus.lintegral_comp`), `OpenCellIntegration` (`openCellMap`, `openCellConstant`,
`lintegral_eq_openCellConstant_inv_mul`, `openCellConstant_eq_lintegral`) and
`DoubleCosetMeasure` (`measure_eq_relIndex_mul`).

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082. I.1, printed p. 240 (PDF p. 6): left invariant measures normalized
by `mes(H ∩ K) = 1`, `G = P K` with `g = u_P(g) m_P(g) k_P(g)`, and the two formulas of (2),

`∫_G f = ∫_{U × M × K} f(u m k) δ_P(m)^{-1} dk dm du`,
`∫_G f = γ(P)^{-1} ∫_{U × M × Ū} f(u m ū) δ_P(m)^{-1} dū dm du`,
`γ(P) = ∫_Ū δ_P(m_P(ū)) dū`.

Proof of Remark (3), printed pp. 240–241 (PDF pp. 6–7): for a compact open `H ⊆ K` with
`H = [∏_{α ∈ Σ_red(P)} (H ∩ U_α)](H ∩ M)[∏_{α ∈ Σ_red(P̄)} (H ∩ U_α)]`, formula (2) applied to the
characteristic function of `H` gives `mes(H) = γ(P)^{-1} mes(U ∩ H) mes(M ∩ H) mes(Ū ∩ H)`,
with `mes(U ∩ H) = [U ∩ K : U ∩ H]^{-1}`, whence
`γ(P) = mes(H)^{-1} mes(M ∩ H) ∏_α [U_α ∩ K : U_α ∩ H]^{-1}`, which depends only on `M`.

The measure `δ_P(m)^{-1} du dm` in the coordinates `u m` is `dm du` in the coordinates `m u`;
this module shows that it is a left Haar measure of `P` with right translation law
`δ_P`, and combines it with the open-cell formula.

## Scope: abstract data and explicit hypotheses

`G` is a topological group with its Borel σ-algebra; `M`, `U`, `P` are subgroups with `M`
normalizing `U` (`hMU`), `U` second countable, and `m u ∈ P` for `m ∈ M`, `u ∈ U` (`hP`);
`leviUnipotentCoord hP (m, u) = m u ∈ P`. The measures `μ_M`, `μ_U` are s-finite and left
invariant (no Haar property unless stated). Hypotheses of individual results:

- `leviUnipotentMeasure_isMulLeftInvariant`: `(m, u) ↦ m u` maps `M × U` onto `P` (`hsurj`).
- `map_mul_right_leviUnipotentMeasure`, `leviUnipotentMeasure_preimage_mul_right`: `μ_M` and `μ_U` are
  also right invariant, and `IsConjModulus hMU μU δ` (`μ_U(m S m^{-1}) = δ(m) μ_U(S)`;
  `δ = δ_P` for Waldspurger); for the second, `S` is measurable.
- `leviUnipotentMeasure_inter`: `K` is a measurable subgroup and `m u ∈ K ↔ m ∈ K ∧ u ∈ K`
  (`hPK`, Waldspurger's `P ∩ K = (M ∩ K)(U ∩ K)` with `M ∩ U = 1`).
- `leviUnipotentMeasure_isHaarMeasure`: `μ_M`, `μ_U` are Haar measures and `(m, u) ↦ m u` is a
  homeomorphism of `M × U` onto `P` (`hhomeo`).
- `lintegral_levi_unipotent_eq`: `IsConjModulus hMU μU δ`.
- `openCellConstant_leviUnipotentMeasure`: `hhomeo`; `μ_M`, `μ_U` right invariant; `IsConjModulus`;
  `K`, `hPK` as above with `μ_M(M ∩ K) = μ_U(U ∩ K) = 1` (`hMK`, `hUK`); and `ℓ : V → M × U` with
  `(ℓ(v)_1 ℓ(v)_2)^{-1} v^{-1} ∈ K` (`hℓ`, the `P`-component of `v^{-1}` in `G = P K`).
- `lintegral_eq_openCell_levi_unipotent`: `P` and `V` locally compact and second countable;
  `μ` a Haar measure on `G` that is also right invariant; `μ_M`, `μ_U`, `μ_V` Haar measures with
  `μ_M`, `μ_U` s-finite; `hhomeo`; the open-cell map `(p, v) ↦ p v^{-1}` an open embedding with
  `μ`-null complement of its image (`hι`, `hnull`); `K` measurable with `0 < μ(K) < ∞`; `F`
  measurable.
- `eq_smul_map_openCellCoord`: the hypotheses of the previous result except `F`.
- `measure_eq_of_openCell_factor`: the hypotheses of `lintegral_eq_openCell_levi_unipotent` and a measurable
  subgroup `H` with `m u v^{-1} ∈ H ↔ m ∈ H ∧ u ∈ H ∧ v ∈ H` (`hH`, `hHf`; Waldspurger's
  factorization of `H`).
- `openCellConstant_eq_relIndex_mul`: those hypotheses and `H ≤ K` of finite index (`hHK`,
  `hKH`).
- `measure_eq_inv_relIndex` (any group `X` with measurable multiplication and a left invariant
  measure `ν`): measurable `Z ≤ Y` of finite index with `ν(Y) = 1`.

None of these hypotheses is proved here for Waldspurger's group.

## Definitions

- `leviUnipotentCoord hP (m, u) = m u`, as a map `M × U → P`.
- `leviUnipotentMeasure hP μM μU`: the image of `μ_M × μ_U` under `leviUnipotentCoord hP` (`dm du`).
- `openCellCoord ((m, u), v) = m u v^{-1}`, the open-cell coordinates of `G`.

## Results

- `continuous_leviUnipotentCoord`: the coordinate map is continuous.
- `leviUnipotentMeasure_isMulLeftInvariant`: `dm du` is left invariant on `P`.
- `map_mul_right_leviUnipotentMeasure`: the image of `dm du` under right translation by
  `m_0 u_0` is `δ(m_0) dm du`; `leviUnipotentMeasure_preimage_mul_right`: equivalently
  `μ_P((· m_0 u_0)^{-1} S) = δ(m_0) μ_P(S)`.
- `leviUnipotentMeasure_inter`: `μ_P(P ∩ K) = μ_M(M ∩ K) μ_U(U ∩ K)`.
- `leviUnipotentMeasure_isHaarMeasure`: `dm du` is a Haar measure of `P`.
- `lintegral_levi_unipotent_eq`: `∫_M ∫_U Φ(m u) du dm = ∫_M δ(m)^{-1} ∫_U Φ(u m) du dm` for
  every `Φ ≥ 0` (the passage to Waldspurger's order `u m` and the factor `δ_P(m)^{-1}`).
- `openCellConstant_leviUnipotentMeasure`: `γ = openCellConstant (dm du) μ_V K = ∫_V δ(ℓ(v)_1) dμ_V`;
  for Waldspurger's data, with `ū = v^{-1}` and
  `ℓ(v) = (m_P(ū), m_P(ū)^{-1} u_P(ū) m_P(ū))` (so that `ℓ(v)_1 ℓ(v)_2 = u_P(ū) m_P(ū)`), this is
  `γ(P) = ∫_Ū δ_P(m_P(ū)) dū` (after the inversion `v ↦ v^{-1}` of `dū`).
- `lintegral_eq_openCell_levi_unipotent` (I.1 (2), second formula, in coordinates):
  `∫_G F dμ = μ(K) γ^{-1} ∫_M ∫_U ∫_V F(m u v^{-1}) dμ_V dμ_U dμ_M` with `γ` as above. With
  `lintegral_levi_unipotent_eq` applied to `Φ(g) = ∫_V F(g v^{-1}) dμ_V` it becomes
  Waldspurger's `γ(P)^{-1} ∫ f(u m ū) δ_P(m)^{-1}` (with `μ(K) = 1`, `ū = v^{-1}` and the
  order of the integrals exchanged by Tonelli).
- `eq_smul_map_openCellCoord`: the same formula as an identity of measures,
  `μ = μ(K) γ^{-1} · ((μ_M × μ_U) × μ_V) ∘ openCellCoord^{-1}`, from which integrals of
  integrable complex functions follow by `integral_map`.
- `measure_eq_of_openCell_factor`: `μ(H) = μ(K) γ^{-1} μ_M(M ∩ H) μ_U(U ∩ H) μ_V(V ∩ H)`
  (Waldspurger's `mes(H) = γ(P)^{-1} mes(U ∩ H) mes(M ∩ H) mes(Ū ∩ H)` when `μ(K) = 1`).
- `openCellConstant_eq_relIndex_mul`: `γ = [K : H] μ_M(M ∩ H) μ_U(U ∩ H) μ_V(V ∩ H)`.
- `measure_eq_inv_relIndex`: `ν(Z) = [Y : Z]^{-1}`. With `μ_X(X ∩ K) = 1` for `X = M, U, V`
  this turns the previous result into `γ = [K : H] ∏_X [X ∩ K : X ∩ H]^{-1}`, Waldspurger's
  expression without the factorization of `[U ∩ K : U ∩ H]` over root subgroups.

## Proof notes

Left invariance: for `p_0 ∈ P` choose `x_0` with `m_0 u_0 = p_0^{-1}`; then
`p_0 (m u) = (m_0 u_0)^{-1} (m u)` is `leviUnipotentShift x_0` in coordinates
(`leviUnipotentMul_shift`), which preserves `μ_M × μ_U`
(`measurePreserving_leviUnipotentShift`). Right translation: `m u m_0 u_0 =
(m m_0)((m_0^{-1} u m_0) u_0)`, so the image of `μ_M × μ_U` is the product of the images under
`m ↦ m m_0` (right invariance) and `u ↦ (m_0^{-1} u m_0) u_0`, which is `δ(m_0) μ_U` by
`IsConjModulus` for `m_0^{-1}` and right invariance. The Haar property transports finiteness
on compact sets and positivity on open sets along the homeomorphism. The value of `γ` is
`openCellConstant_eq_lintegral` with `d(p) = δ` of the `M`-coordinate of `p`, and the formula in
coordinates is `lintegral_eq_openCellConstant_inv_mul` for `dm du` followed by
`lintegral_map` and Tonelli. The change to the order `u m` uses `m u = (m u m^{-1}) m` and
`IsConjModulus.lintegral_comp`. For a factorized `H`, the indicator of `H` at `m u v^{-1}` is
the product of the indicators of `M ∩ H`, `U ∩ H`, `V ∩ H`, so the triple integral is the
product of their measures; comparing with `μ(K) = [K : H] μ(H)` and cancelling `μ(H)` gives the
index expression of `γ`.

## Open obligations

For Waldspurger's data: the homeomorphism `M × U ≅ P`, the decomposition of `P ∩ K`, the Haar
measures, their unimodularity on `M` and `U` and normalizations, the modulus relation for
`δ_P`, the open-cell embedding and its conull image, the Iwasawa component `ℓ`, the inversion
invariance of `dū`, the existence of a factorized `H`, the factorization
`[U ∩ K : U ∩ H] = ∏_α [U_α ∩ K : U_α ∩ H]` over root subgroups, and hence Remark (3) (`γ(P)`
depends only on `M`) are not proved here.
