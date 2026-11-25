# The zeta integral of the test function attached to a stratum

## Setting

`K` is a `p`-adic field (`PadicField p`) with its canonical topology, valuation and local-field
structure, `GeneralLinear (n + 1) K.Carrier` carries its Borel measurable structure, and
`RankinSelberg.generalLinearHaar K.Carrier n` is the Library Haar measure on `GL_{n+1}(K)` used
by the `p`-adic Godement–Jacquet integrals (`GodementJacquet.Padic.matrixIntegral`). `𝓛` is a
lattice chain in `K^{n+1}`, `unitSubgroup K 𝓛 k` is the published subgroup `U^k(𝔄(𝓛))` of
`GL_{n+1}(K)` (module `Langlands.BushnellKutzko.NormalizedLevel`) and
`LatticeChain.matrixFiltration 𝓛 k` is the additive group of matrices of `𝔓^k(𝓛)` (module
`FourierSupport`). `ψ` is a Library `UnitaryAdditiveCharacter K.Carrier`.

## Declarations

- `toLin'_sub_one`, `coe_toLin_eq_toLin'`: bookkeeping between matrices and their linear maps.
- `mem_unitSubgroup_iff_sub_one_mem`: for `k ≥ 1`, `g ∈ U^k(𝔄(𝓛))` if and only if
  `g - 1 ∈ 𝔓^k(𝓛)` (as matrices).
- `image_val_unitSubgroup`: for `k ≥ 1`, the matrices of the elements of `U^k(𝔄(𝓛))` are exactly
  the matrices `y` with `y - 1 ∈ 𝔓^k(𝓛)`.
- `isOpen_one_add_matrixFiltration`, `isCompact_one_add_matrixFiltration`: for `k ≥ 1`, the set
  `{y | y - 1 ∈ 𝔓^k(𝓛)}` of `(n+1) × (n+1)` matrices is open and compact.
- `isLocallyConstant_character_comp`: `y ↦ ψ(L y)` is locally constant for every continuous
  additive map `L` to `K`.
- `isLocallyConstant_twistedIndicator`, `hasCompactSupport_twistedIndicator`: for `k ≥ 1`, the
  function `twistedIndicator ψ (𝓛.matrixFiltration k) b'` of `FourierSupport`, that is
  `y ↦ 1[y - 1 ∈ 𝔓^k(𝓛)] ψ(-tr(b' (y - 1)))`, is locally constant with compact support.
- `stratumTest K 𝓛 hk ψ b'` (definition): this function as a Library
  `GodementJacquet.MatrixTestFunction n K.Carrier` (a Schwartz–Bruhat function on all
  `(n+1) × (n+1)` matrices); `stratumTest_apply` unfolds it.
- `stratumCoefficient K σ ℓ w` (definition): the coefficient `g ↦ ℓ(σ(g) w)` of a smooth functional
  `ℓ` and a smooth vector `w` of a complex representation `σ` of `GL_{n+1}(K)`, as an element of
  the Library span `GodementJacquet.biSmoothMatrixCoefficients σ`.
- `matrixIntegral_stratumTest`: let `k ≥ 1` and let `w` satisfy
  `σ(g) w = ψ(tr(b' (g - 1))) w` for all `g ∈ U^k(𝔄(𝓛))`. Then for every complex `s` the matrix
  integral `∫_{GL_{n+1}(K)} Φ(g) ℓ(σ(g) w) |det g|^s dg` (`Φ = stratumTest`) converges
  absolutely (`GodementJacquet.Padic.MatrixConverges`) and equals `vol(U^k(𝔄(𝓛))) ℓ(w)`, the
  volume taken for `generalLinearHaar` (`GodementJacquet.Padic.matrixIntegral`).
- `generalLinearHaar_real_unitSubgroup_pos`: `vol(U^k(𝔄(𝓛)))` is a positive real number.
- `hasShiftedRationalValue_stratumTest`: under the hypotheses of `matrixIntegral_stratumTest`,
  `GodementJacquet.HasShiftedRationalValue` holds for `Φ`, the coefficient and the constant
  rational function `vol(U^k(𝔄(𝓛))) ℓ(w)`, with the residue cardinality of `K`, the normalized
  absolute value and `generalLinearHaar`.

In the intended use, `ℓ(w) ≠ 0`, so the rational value is a nonzero constant; this is the input
`R = C r` of the functional equation in `ShellIdentity`.

## Provenance

The computation is the standard first step of the Godement–Jacquet treatment of a representation
containing a character of a compact open subgroup: the test function is the conjugate of the
character on `U^k(𝔄(𝓛))`, extended by zero, so the zeta integrand is constant on `U^k(𝔄(𝓛))`.
It is internal to the proof of T2. Compare Bushnell (1987), Theorem 3, and
Bushnell–Fröhlich (1985), (3.3.8), for the use of such test functions.
The structure of the proof follows the Library proof `exists_matrixIntegral_one`
(module `Langlands.Representation.GodementJacquet.MatrixUnitValueProof`), which treats the
indicator of `GL_{n+1}(𝔬_K)`.

## Proof

`mem_unitSubgroup_iff_sub_one_mem` unfolds `unitSubgroup` (`mem_unitSubgroup`): one direction is
the third condition of membership; for the other, `LatticeChain.exists_mem_unitFiltration`
(Library) gives a unit `u ∈ U^k(𝓛)` with `u = 1 + toLin'(g - 1)`, which equals the image of `g`.
`image_val_unitSubgroup` uses the same lemma to show that `y` is invertible when
`y - 1 ∈ 𝔓^k(𝓛)` (its linear map is the unit `u`), and then applies the first lemma to the unit
`y`.

Openness and compactness of `1 + 𝔓^k(𝓛)` follow by transporting `isOpen_unitSubgroup` and
`isCompact_unitSubgroup` (published module `FundamentalStratumLevelCore`) along the
open embedding `GL_{n+1}(K) → M_{n+1}(K)` (`RankinSelberg.isOpenEmbedding_generalLinear_val`) and
the continuous map `Units.val`.

`isLocallyConstant_character_comp` uses the Library lemma
`RankinSelberg.TwoBlockDeformation.character_eq_one_mem_nhds` (`ψ = 1` near `0`) and continuity of
`L`. The twisted indicator is locally constant because `1 + 𝔓^k(𝓛)` is open and closed: near a
point of the set it agrees with `y ↦ ψ(-tr(b'(y - 1)))`, near a point of the complement it is `0`.
Its support lies in the compact set `1 + 𝔓^k(𝓛)`.

For `matrixIntegral_stratumTest`, the integrand is computed pointwise. For `g ∈ U^k(𝔄(𝓛))`,
`Φ(g) = ψ(-tr(b'(g - 1)))`, `ℓ(σ(g) w) = ψ(tr(b'(g - 1))) ℓ(w)` by the hypothesis on `w`, and
`|det g| = 1` because `U^k(𝔄(𝓛))` is compact (Library `determinantNorm_eq_one_of_mem_compact`), so
the integrand is `ℓ(w)`. For `g ∉ U^k(𝔄(𝓛))`, `g - 1 ∉ 𝔓^k(𝓛)` and `Φ(g) = 0`. Hence the
integrand is the indicator of `U^k(𝔄(𝓛))` times `ℓ(w)`; the subgroup is open (measurable) and
compact (finite measure), which gives integrability and the value
(`integral_indicator_const`). Positivity of the volume: open sets containing `1` have positive
Haar measure, compact sets finite measure.

`hasShiftedRationalValue_stratumTest` takes convergence on every half-plane (bound `0`) and, for
the rational continuation, the constant rational function, whose denominator `1` does not vanish
and whose value is the integral at `s + n/2` (`jpssShift`).
