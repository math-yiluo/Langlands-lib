# Harris's level `K(N)_p` at a split prime

Author: Worker 19.

This module assembles Harris's `p`-adic level

`K(N)_p = C_v^{N,0} × ∏_{j>1} C^(j) × ℤ_pˣ`

for the unitary similitude group of the published Harris setting, at a
degree-one place `𝔭` of the imaginary quadratic field, when the algebra is a
division algebra at the places of the CM field above `𝔭`. It applies the
local levels of `LocalDivisionLevels` at each place `w` above `𝔭` and the
product form `splitPlaceLevel` of `HarrisSplitPrimeFactorLevels`.

## Source

Harris (1997), Section 2, printed p. 88 (PDF p. 14): with `p = 𝔭₁ · 𝔭₂`
split in `𝒦₀`, "we assume `ℬ` to be a division algebra at every `v_i^(j)`";
"Let `𝒪_{B^opp}` be the maximal order in `B^opp` and let `m_v` denote the
maximal ideal of the ring `O_F` of integers in `F`. Let `C_v = 𝒪_{B^opp}ˣ`
… and for any integer `N ≥ 1`, let `C_v^{N,0} = 1 + (m_v)^N 𝒪_{B^opp} ⊂ C_v`."
Printed p. 89 (PDF p. 15): "For `j > 1`, we let `C_v^(j)` denote the (unique)
maximal compact subgroup of `GG(K_1^(j))`, and let
`C(N)_p = C_v^{N,0} × ∏_{j>1} C_v^(j) × ℤ_pˣ ⊂ GG` with respect to the
factorization (2)."

Harris (1998), Appendix, printed p. 206 (PDF p. 30): "Starting in Sect. 2 of
[H1] `ℬ` was assumed to be a division algebra at every `v_i^(j)`. Moreover,
the `p`-level subgroup `C(N)_p` was assumed to have a factorization
(A.2) `C(N)_p ≅ C_v^{N,0} × ∏_{j>1} C_p^(j) × ℤ_pˣ`".

Harris (1999), Section 4, printed p. 309 (PDF p. 11): `K(N)_p = C_v^{N,0} ×
∏_{j>1} C^(j) × ℤ_pˣ`, with `C_v^{N,0}` "the level `N` subgroup defined in
[H2, (A.2)]".

## Declarations

All declarations are in namespace `Langlands.Shimura`.

### Completions

For a number field `K` and a finite place `w`:

- `completionNormedField w` is the nontrivially normed field structure of
  `K_w` given by its valuation (Mathlib's `Valued.toNontriviallyNormedField`);
  its topology is the topology of `K_w`.
- The existing `Global.AdelicSpaceLevelTopologyProof.finiteCompletion_locallyCompactSpace K w`
  supplies local compactness of `K_w`, since the
  completed integers are compact (published `isCompact_adicCompletionIntegers`)
  and open.

### Local levels

Let `A` be a `K`-algebra finite over `K`.

- `IsDivisionAt A w` is the proposition that `K_w ⊗[K] A` is nontrivial and
  every nonzero element is a unit: `K_w ⊗[K] A` is a division algebra
  (Harris's hypothesis that `ℬ` is a division algebra at `w`).
- `placeDivisionRing A w h` is the resulting division ring structure
  (Mathlib's `DivisionRing.ofIsUnitOrEqZero`; it keeps the ring structure).
- `placeMaximalCompactLevel A w h` is
  `LocalDivision.maximalCompactLevel` for `K_w ⊗[K] A` over `K_w` (with the
  normed structure above and the `K_w`-module topology): the unique maximal
  compact subgroup `O_{D_w}ˣ` of `(K_w ⊗[K] A)ˣ`, as a level of
  `FactorUnits K A K_w`. `mem_placeMaximalCompactLevel`: `x` lies in it iff
  `|x| ≤ 1` and `|x⁻¹| ≤ 1` for the normalized determinant norm.
- `placeCongruenceLevel A w h r hr0 hr`, for `0 < r < 1`, is
  `LocalDivision.congruenceLevel`: the units `x` with `|x - 1| ≤ r`
  (`mem_placeCongruenceLevel`); `placeCongruenceLevel_le`: it is contained in
  `placeMaximalCompactLevel`.
- `mem_placeCongruenceLevel_iff_exists`: for `ϖ ≠ 0` in `K_w` and radius
  `‖ϖ‖^N < 1`, membership means `x = 1 + ϖ^N y` with `y` in the integer ring
  of `K_w ⊗[K] A`. For a uniformizer `ϖ` of `K_w` and `N ≥ 1` this is
  Harris's `C_v^{N,0} = 1 + (m_v)^N 𝒪`.

### Harris's level

In the Harris setting of `HarrisSplitPrimeFactorLevels` (`ι : F →+* K`, a
place `𝔭` of `F` above `v` with bijective completion map `h𝔭`, `A` finite
over `ℚ` with the tower `ℚ → K → A`):

- `moduleFinite_of_rat`: `A` is finite over `K`.
- `harrisLocalLevels A ι v 𝔭 hdiv w₀ r hr0 hr`, for `hdiv : ∀ w, IsDivisionAt A w`
  over the places `w` of `K` above `𝔭` and a distinguished place `w₀`, is the
  family of local levels: `placeCongruenceLevel` of radius `r` at `w₀` and
  `placeMaximalCompactLevel` at every other `w`.
- `σ.harrisLevel ι v 𝔭 h𝔭 hdiv w₀ r hr0 hr`, for
  `σ : SecondKindInvolution E K A`, is `σ.splitPlaceLevel` of this family:
  Harris's `K(N)_p = C_v^{N,0} × ∏_{j>1} C^(j) × ℤ_pˣ` of `GG(ℚ_v)` when
  `r = ‖ϖ‖^N` for a uniformizer `ϖ` of `K_{w₀}`.
- `mem_harrisLevel`: a point `g` lies in it exactly when the `w₀`-component of
  `(σ.splitPlacePoints ι v 𝔭 h𝔭 g).1` lies in the congruence level, every
  other component lies in the maximal compact level, and the multiplier lies
  in `ℤ_vˣ`.

## Scope

The division hypothesis is an input; whether a given global algebra is
division at the places above `𝔭` (Harris's invariant `1/n` at the
distinguished place) is not proved. The radius `r` and the distinguished place
are inputs; the identification of `w₀` with Harris's distinguished place `v`
(through the CM type) is not formalized. Global levels `K(N, m)` with this
`K(N)_p` are obtained from `HarrisInnerFormLevels` or
`HarrisSplitPrimeLevels` by taking the corresponding level of
`(ℚ_v ⊗[F, u] A)ˣ`.

## Provenance

Derived from Harris (1997), Section 2, printed pp. 88-89, Harris (1998),
Appendix, (A.2) on printed p. 206, and Harris (1999), Section 4, printed p. 309,
all read in the original. The packaging through the place decomposition and
the generic local levels is an implementation choice.

Source IDs and SHA-256 fingerprints:

- `harris-1997-drinfeld-cohomology`:
  `aea284b917442459028b710dbfd9ae537631490504f3bc6d54a1e76ee697e0d9`.
- `harris-1998-local-langlands`:
  `7934239ea37d0b91f741ae70c2ac157fe5d619cda4dd992ac24e39ae460c375b`.
- `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`:
  `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Formal dependencies: `Langlands.Shimura.Unitary.HarrisSplitPrimeFactorLevels`,
`Langlands.Shimura.Unitary.LocalDivisionLevels`, the published
`Langlands.Global.IntegralFiniteAdeles` and
`Langlands.Global.AdelicSpaceLevelTopologyProof`, and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435` under Lean 4.34.0, in particular
`Valued.toNontriviallyNormedField`, `DivisionRing.ofIsUnitOrEqZero`,
`IsCompact.locallyCompactSpace_of_mem_nhds_of_addGroup` and
`Valued.isOpen_valuationSubring`.
