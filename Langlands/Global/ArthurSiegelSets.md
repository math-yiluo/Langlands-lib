# Siegel sets, truncated Siegel sets and the functions `F^P(x, T)`

Module `Langlands.Global.ArthurSiegelSets`, namespace `Langlands.Global.ArthurTruncation`.
The propositions about these objects are stated in
`Langlands.Global.ArthurSiegelSetsStatement` (see its Markdown). The module uses the data and the
height `H_0` of `Langlands.Global.ArthurTruncation` (see its Markdown) and the published L1
ordered factor products of `Langlands.Global.AdelicSiegelFactors`. It proves one lemma,
`mem_siegelSet_iff`, which unfolds the Siegel set.

## Sources

- J. Arthur, *An introduction to the trace formula* (2005), in the volume registered as
  `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura` (PDF page = printed page + 12):
  - §8, p.37: for `T_1 ∈ 𝔞_0` and a compact subset `ω` of `N_{P_0}(𝔸) M_{P_0}(𝔸)^1`, the Siegel
    set `S^G(T_1, ω) = {x = pak : p ∈ ω, a ∈ A_0(ℝ)^0, k ∈ K, β(H_{P_0}(a) − T_1) > 0, β ∈ Δ_0}`;
    for `T` with `β(T)` large, the truncated Siegel set
    `S^G(T_1, T, ω) = {x ∈ S^G(T_1, ω) : ϖ(H_{P_0}(x) − T) ≤ 0, ϖ ∈ Δ̂_0}`; `F^G(x, T)` is the
    characteristic function of the projection of `S^G(T_1, T)` onto `G(ℚ)\G(𝔸)`;
  - pp.37–38: "More generally, suppose that `P` is a standard parabolic subgroup. We define the
    sets `S^P(T_1)`, `S^P(T_1, T)` and the characteristic function `F^P(x, T)` exactly as above,
    but with `Δ_0`, `Δ̂_0` and `G(ℚ)\G(𝔸)` replaced by `Δ_0^P`, `Δ̂_0^P` and `P(ℚ)\G(𝔸)`";
  - §13, p.70: `φ` on `G(ℚ)\G(𝔸)^1` is rapidly decreasing if for every positive integer `N` and
    every Siegel set `S = S^G(T_1)` there is `C` with `|φ(x)| ≤ C ‖x‖^{−N}` for `x ∈ S ∩ G(𝔸)^1`;
    the height `‖x‖ = ‖r(x)‖` comes from a rational injection `r : G → GL(m)` with compact sublevel
    sets.
- J. Arthur, *A trace formula for reductive groups I* (1978), registered as
  `arthur-1978-trace-formula-reductive-groups-I`, §6, printed p.941: the same sets
  `S^{P_1}(T_0, ω)` (with `ω ⊆ N_0(𝔸) M_0(𝔸)^1` compact), `S^{P_1}(T_0, T, ω)` and `F^{P_1}(x, T)`,
  "the characteristic function of the set of `x ∈ G(𝔸)` such that `δx` belongs to
  `S^{P_1}(T_0, T, ω)` for some `δ ∈ P_1(ℚ)`".

Arthur works over `ℚ`; here `F` is a number field, as in the L1 Siegel sets and in Lapid 2011, §2.

## Definitions

Throughout, `P` is the standard parabolic subgroup with `Δ_0^P = SP` (a finite subset of
`simpleFinset ν hG hi = Δ_0`), and `H_0 = height hi hK hρ` is the height of
`Langlands.Global.ArthurTruncation` (the Iwasawa height of the compact subgroup `K` for `P_0`,
read in `𝔞_0 = V T`).

- `positiveTorusMap F i`: `A_0(ℝ)^0 → G(𝔸)`. It is the published `AdelicSiegelFactors.positiveMap`
  for the torus `T` itself (`T₀ = T`, `j = 𝟙`), on the published intrinsic positive subgroup
  `PositiveRealTorus.intrinsicSubgroup F T` (the points all of whose characters are positive
  scalar ideles, the group `A_T(ℝ)^0` of Mœglin–Waldspurger I.2.1 for split `T`).
- `siegelChamber hi hK hρ SP T₁`: the `a ∈ A_0(ℝ)^0` with `β(H_0(a) − T_1) > 0` for every
  `β ∈ Δ_0^P`, where `β(H) = eval T β H` is the pairing of `X(T)` with `V T`.
- `siegelSet hi hK hρ C SP T₁` is `S^P(T_1, ω)`: the published ordered factor product
  `AdelicSiegelFactors.productSet` of the compact factors `C` (for the canonical standard factors
  `canonicalStandardFactors`, that is, `N_0 = Standard.unipotentScheme i ν ∅` and
  `M_0 = Standard.leviScheme i ν ∅`) over `siegelChamber`. Its elements are the products
  `n m a k` with `n ∈ Ω_N ⊆ N_0(𝔸)`, `m ∈ Ω_M ⊆ M_0(𝔸)^1` (both compact), `a` in the chamber and
  `k ∈ C.compactSubgroup` (`mem_siegelSet_iff`). So `ω = Ω_N Ω_M`. The statements take
  `C.compactSubgroup = K`.
- `truncatedSiegelSet hG hi D hK hρ C SP T₁ Tp` is `S^P(T_1, T, ω)`: the `x ∈ S^P(T_1, ω)` with
  `ϖ_β(H_0(x) − T) ≤ 0` for every `β ∈ Δ_0^P`, where `ϖ_β = ArthurRelative.weight hG hi ν D SP β`
  is the weight of `Δ̂_0^P` attached to `β` (the coefficient of `β^∨` in the `𝔞_0^P`-component,
  `ArthurRelative.weight_coroot`). For `P = G` these are the weights `Δ̂_0`.
- `siegelIndicator hG hi D hK hρ C SP T₁ Tp x ∈ {0, 1}` is `F^P(x, T)`: it is `1` exactly when
  `δx ∈ S^P(T_1, T, ω)` for some `δ` in the image of `P(F)` in `G(𝔸)`
  (`parabolicRationalImage`), as in Arthur 1978. As a function on `G(𝔸)` it is left
  `P(F)`-invariant, and it is the characteristic function of the projection of `S^P(T_1, T, ω)`
  to `P(F)\G(𝔸)`. It is `ℤ`-valued, like `ArthurRelative.tau`.
- `IsRapidlyDecreasing hG hi hK hρ rho φ`: for every compact factor data `C` with
  `C.compactSubgroup = K`, every `T_1 ∈ 𝔞_0` and every `n ∈ ℕ` there is `B` with
  `‖φ(x)‖ ≤ B ‖x‖^{−n}` for every `x ∈ S^G(T_1, ω) ∩ G(𝔸)^1` (`normOneSubgroup F G`), where `‖x‖`
  is the published `RepresentationGrowth.adelicSourceNorm F G rho x` of a matrix representation
  `rho`. This is Arthur's definition (p.70) for the Siegel sets with `ω = Ω_N Ω_M`.

## Correspondence with the source

- **Condition on `a`.** Arthur writes `β(H_{P_0}(a) − T_1) > 0`; `siegelChamber` evaluates the
  height `H_0` at the image of `a` in `G(𝔸)`, which is `H_{P_0}(a)`. Arthur notes that the
  condition amounts to `τ_{P_0}(H_{P_0}(x) − T_1) = 1` for `x = pak`, because `H_{P_0}` vanishes on
  `N_0(𝔸) M_0(𝔸)^1` and is right `K`-invariant; that remark is not used in the definitions.
- **The compact set `ω`.** Arthur allows any compact `ω ⊆ N_0(𝔸) M_0(𝔸)^1`. The definitions use
  the products `Ω_N Ω_M` of the published L1 compact factor data. Every compact
  `ω ⊆ N_0(𝔸) M_0(𝔸)^1` is contained in such a product (the multiplication map
  `N_0(𝔸) × M_0(𝔸)^1 → N_0(𝔸) M_0(𝔸)^1` is a homeomorphism); this is not formalized. The
  statements quantify over these products.
- **The height `‖x‖`.** Arthur's `‖x‖ = ∏_v ‖r(x)_v‖_v` uses the matrix entries of `r(x)`. The
  published `adelicSourceNorm` is the local product of the norms of the matrix and its inverse.
  The two are polynomially equivalent (Arthur's (13.3), `‖x^{−1}‖ ≤ C_0 ‖x‖^{N_0}`), so rapid
  decrease is the same for both. The statements require `rho` to be a closed embedding
  (`IsClosedSubgroup rho`), which gives compact sublevel sets
  (`RepresentationGrowth.isCompact_adelicHeightSublevel`).
- **`G(𝔸)^1`.** Arthur's functions live on `G(ℚ)\G(𝔸)^1`; here they are functions on `G(𝔸)`, and
  rapid decrease is tested on `S ∩ G(𝔸)^1`, as in Arthur.

## Provenance

The sets and functions are Arthur's (source: Arthur 2005, §8 and p.70; Arthur 1978, §6). The
encoding through the L1 ordered factor products, the standard representatives, the height `H_0`
read in `V T` and the source norm of a matrix representation are derived formulations, explained
above.
