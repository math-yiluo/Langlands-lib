# Harris's pro-`p` levels `H_p` and `H(m)`

Author: Worker 19.

This module constructs Harris's level `H_p`: an open normal pro-`p` subgroup
of a compact open `C_p`, contained in a level `K_p`. It works for the
similitude points of an algebra with involution at a finite place of a
number field. Over `ℚ` it also builds the global level
`H(m) = K(m)^p × H_p` of the finite adelic points. The general construction
is in `Langlands.Shimura.ProPLevels`.

## Source

Harris (1999), Section 4, printed p. 310 (PDF p. 12): "To continue, we fix a
compact open subgroup `K_p ⊂ GJ_p` contained in a fixed maximal compact
subgroup `C_p`. [...] Let `H_p` be an open normal pro-`p` subgroup of `C_p`
contained in `K_p`, and let `H(m) = K^{ℓ,p} × K_ℓ(m) × H_p`; when `m = 1` we
just write `H`."

Harris (1999), Section 4, printed p. 309 (PDF p. 11): "write
`K(m)^p = K^{ℓ,p} × K_ℓ(m)`". So `H(m) = K(m)^p × H_p`.

## Declarations

All declarations are in namespace `Langlands.Shimura`.

- `norm_natCast_adicCompletion_lt_one w hp`: let `K` be a number field and `w`
  a finite place of `K` whose prime ideal contains the integer `p`. Then
  `‖p‖ < 1` in the completion `K_w`, normed by the published
  `completionNormedField w`.

### Local levels

Let `K` be a number field, `σ : AlgebraInvolution K A` with `A` finite over
`K`, and `w` a finite place of `K`. The published local points
`σ.Points K_w` are the pairs `(g, c)` with `g ∈ (K_w ⊗[K] A)ˣ`,
`c ∈ K_wˣ` and `g σ(g) = c`. Let `ρ` be the left regular representation of
`K_w ⊗[K] A` with the operator norm (`regularRepresentation` of
`ProPLevels`).

- `AlgebraInvolution.totallyDisconnectedSpace_points` (instance):
  `σ.Points K_w` is totally disconnected.
- `σ.principalPoints w` is the subgroup of points `(g, c)` with
  `‖ρ(g) - 1‖ ≤ 1/2` and `‖c - 1‖ ≤ 1/2` (`mem_principalPoints`).
- `isOpen_principalPoints`: it is open.
- `isTopologicallyPTorsion_principalPoints`: if the prime of `w` contains
  `p`, it is topologically `p`-torsion. Both factors are, by `‖p‖ < 1` in
  `K_w`.
- `σ.proPLevel w hp hpw C hL`: let `p` be prime with `p` in the prime of `w`,
  `C` a compact open level of `σ.Points K_w` and `L` an open subgroup. Then
  `proPLevel` is a `NormalProPLevel p C L`: a compact open level contained in
  `L` and in `C`, normal in `C` and pro-`p`. It is the normal core in `C` of
  `L ∩ principalPoints ∩ C` (`NormalProPLevel.ofNormalCore`).
- `nonempty_normalProPLevel` states the existence.

### Global levels over `ℚ`

Let `σ : AlgebraInvolution ℚ A` with `A` finite over `ℚ`, `p` a prime and
`v` the finite place of `ℚ` dividing `p`. The published splitting
`finiteAdelicPointsSplit` identifies `σ(A_f)` with
`σ(∏_{w ∣ p} ℚ_w) × σ(A_f^p)`. The published `dividingPrimePointsEquiv`
identifies the first factor with `σ(ℚ_v)`.

- `σ.localAdelicLevel p hp v L_p L'`: for a level `L_p` of `σ(ℚ_v)` and a
  level `L'` of `σ(A_f^p)`, the level `L_p × L'` of `σ(A_f)`, transported
  through these identifications.
- `mem_localAdelicLevel`: `g` lies in it if and only if its local image
  `finiteLocalMap v g` lies in `L_p` and its prime-to-`p` component lies in
  `L'`.
- `localAdelicLevel_mono`: it is monotone in `L_p`.
- `σ.harrisProPLevel p hp v K_p C_p` is Harris's `H_p`: the
  `NormalProPLevel p C_p K_p` given by `proPLevel`, for compact open levels
  `K_p` and `C_p` of `σ(ℚ_v)`.
- `σ.harrisProPAdelicLevel p hp v K_p C_p K_m` is Harris's
  `H(m) = K(m)^p × H_p`. Here `K_m` is the prime-to-`p` level `K(m)^p` and
  `H_p = harrisProPLevel K_p C_p`.
- `harrisProPAdelicLevel_le`: `H(m) ⊆ K(m)^p × K_p`.

## Scope

- **Generic group.** Harris works with `GJ`, the similitude group of the
  division algebra `𝒟` with involution. The module applies to any
  `AlgebraInvolution`, in particular to `𝒟` with its involution.
- **One choice of `H_p`.** `proPLevel` is one explicit `H_p`. Harris allows
  any open normal pro-`p` subgroup of `C_p` contained in `K_p`. The structure
  `NormalProPLevel` records exactly these properties, so results can be
  stated for an arbitrary `H_p`.
- **Hypotheses on `K_p` and `C_p`.** `harrisProPLevel` takes `K_p` and `C_p`
  as arbitrary compact open levels. It does not require `K_p ⊆ C_p` or `C_p`
  maximal; Harris's setting is the special case. When `K_p ⊆ C_p` fails,
  `H_p` still lies in both.
- **Level `m`.** `K(m)^p` is an input. The ℓ-adic levels
  `K^{ℓ,p} × K_ℓ(m)` of Harris are not constructed here.
- **Not covered.** The fixed-point condition (4.5) and the decomposition
  (4.6) are not treated.

## Provenance

Derived from Harris (1999), Section 4, printed pp. 309-310, read in the
original. The choice of principal points of radius `1/2` with respect to the
left regular representation is an implementation choice; any radius in
`(0, 1)` works. The global level is assembled from the published splitting
of the finite adelic points.

Source ID and SHA-256 fingerprint:

- `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`:
  `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Formal dependencies:

- the companion module `Langlands.Shimura.ProPLevels` (same candidate);
- the published `Langlands.Shimura.Unitary.HarrisDivisionLevels`
  (`completionNormedField`), and through it:
  - `Langlands.Shimura.Unitary.HarrisSplitPrimeLevels`
    (`dividingPrimePointsEquiv`);
  - `Langlands.Shimura.Unitary.PointsSplit` (`finiteAdelicPointsSplit`,
    `dividingLocalMap`);
  - `Langlands.Shimura.Unitary.Adelic` (`Points`, `finiteLocalMap`);
  - `Langlands.Shimura.PartialLevelTower` (`CompactOpenLevel.prod`);
  - `Langlands.Shimura.PEL.TraceSimilitudesLevels`
    (`CompactOpenLevel.transport`);
- Mathlib `5ed2965256430c3649e86755f9576b54eca72435` under Lean 4.34.0.

The Mathlib results used include `valuedAdicCompletion_eq_valuation'`,
`valuation_lt_one_iff_mem` and `Valued.toNormedField.norm_lt_one_iff`.
