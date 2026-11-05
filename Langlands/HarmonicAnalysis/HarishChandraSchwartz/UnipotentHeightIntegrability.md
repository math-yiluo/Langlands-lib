# Integrability of negative powers of the height on dynamic unipotent subgroups

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.UnipotentHeightIntegrability`.
The measure-theoretic part (`HasPolynomialSublevelVolume` and its three theorems) is in the
namespace `Langlands.HarishChandraSchwartz`. The local-field theorems are in the namespace
`Langlands.GroupScheme.MatrixRepresentation`.

## Purpose and provenance

Provenance: internal. Convergence proofs for intertwining integrals bound the integrand on an
opposite unipotent group `Ū(F)` by a negative power of the height and then need that power to be
integrable for Haar measure. In Waldspurger, *La formule de Plancherel pour les groupes
p-adiques, d'après Harish-Chandra* (2003), integrability of this kind is used in II.3 and IV.1.
It is not stated there in the form proved here. This module derives it from the public
polynomial volume bound `exists_measure_rationalMatrixNorm_le_mul_pow` (module
`UnipotentHeightVolume`) by a dyadic decomposition. It does not transcribe a proof from the
source.

## Setting and notation

- `X` is a measurable space, `ν` a measure on `X` and `f : X → ℝ` a function (the weight).
- `x ^ y` for real `x, y` is `Real.rpow`; `ENNReal.ofReal` maps `ℝ` to `[0, ∞]`.
- In the local-field part, `F` carries `[ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]`, and `F` is normed by
  `LocalField.residueNormalizedAbsoluteValue F`. `G` is a group scheme over `Spec F` with
  `G.X.left` affine and `G` locally of finite type over `F`. `G(F)` is `rationalPoints G` with
  the canonical point topology `rationalPointTopology F G.X`, a topological group (public
  `rationalPoint_isTopologicalGroup`).
- For a representation `ρ : G ⟶ GL_n` on a finite nonempty type `n`, `rationalMatrixNorm F ρ g`
  is `glNorm (ρ.rationalMatrix g)`, the largest absolute value of an entry of `ρ(g)` or
  `ρ(g)⁻¹` (public `RationalModerateGrowthStatement`). It is at least `1` (public
  `one_le_rationalMatrixNorm`). `IsClosedSubgroup ρ₀` says that `ρ₀` is a closed immersion.
- `χ : 𝔾_m ⟶ G` is a cocharacter and `χ(t) = gmRationalPoint t ≫ χ.hom.hom ∈ G(F)` for
  `t ∈ Fˣ`. The subgroup `Ū` is `Dynamic.unipotent` of the cocharacter `t ↦ χ(t⁻¹)`, written in
  Lean as `CommGroupScheme.groupHom (Gm.powerHom _ (-1)) ≫ χ`.

## Declarations

### Polynomial sublevel volume (measure-theoretic part)

- `HasPolynomialSublevelVolume ν f C D` (definition, a `Prop`), for `C : ℝ` and `D : ℕ`:
  `ν {x | f x ≤ R} ≤ ENNReal.ofReal (C * R ^ D)` for every real `R ≥ 1`.

In the next three theorems, `hV : HasPolynomialSublevelVolume ν f C D`, `f` is measurable,
`1 ≤ f x` for every `x`, and `s` is a real number with `D < s`.

- `HasPolynomialSublevelVolume.lintegral_rpow_neg_lt_top`:
  `∫⁻ x, ENNReal.ofReal (f x ^ (-s)) ∂ν < ⊤`.
- `HasPolynomialSublevelVolume.integrable_rpow_neg`: `x ↦ f x ^ (-s)` is `ν`-integrable.
- `HasPolynomialSublevelVolume.integrable_of_norm_le`: for a normed additive group `E`, an
  a.e.-strongly measurable `φ : X → E` and `K : ℝ` with `‖φ x‖ ≤ K * f x ^ (-s)` for
  `ν`-almost every `x`, `φ` is `ν`-integrable.

### Local fields

- `continuous_rationalMatrixNorm`: for every representation `ρ` of `G` on a finite nonempty
  type, `g ↦ rationalMatrixNorm F ρ g` is continuous on `G(F)`.

In the next two theorems, `χ` is a cocharacter of `G`, `ρ₀` is a closed representation of `G`
on `Fin N` with `N` positive, and `H` is a subgroup of `G(F)` such that

- `H` is closed in `G(F)`,
- `H ≤ Ū(F)`, and
- `χ(t)` lies in the normalizer of `H` for every `t ∈ Fˣ`.

`H` carries any measurable structure for which it is a Borel space, and `ν` is a regular Haar
measure on `H`. These are exactly the hypotheses of the public
`exists_measure_rationalMatrixNorm_le_mul_pow`.

- `exists_hasPolynomialSublevelVolume_rationalMatrixNorm`: there are `C : ℝ` and `D : ℕ` with
  `HasPolynomialSublevelVolume ν (fun x : H => rationalMatrixNorm F ρ₀ x) C D`.
- `exists_integrable_rationalMatrixNorm_rpow_neg` (main theorem): there is `D : ℕ` such that
  for every real `s > D` the function `x ↦ rationalMatrixNorm F ρ₀ x ^ (-s)` on `H` is
  `ν`-integrable.

## Proofs as implemented

**Dyadic bound (`lintegral_rpow_neg_lt_top`).** Since `D ≥ 0`, `s > 0`. Put `r = 2 ^ (-s)` and
`S k = {x | f x ≤ 2 ^ k}`, a measurable set because `f` is measurable. Let `g k` be the indicator
of `S k` with constant value `ofReal (2 ^ s) * ofReal r ^ k`.

1. *Pointwise.* For `x`, Mathlib's `exists_nat_pow_near` (with `1 ≤ f x`) gives `n` with
   `2 ^ n ≤ f x < 2 ^ (n + 1)`, so `x ∈ S (n + 1)`. Since `-s ≤ 0`,
   `Real.rpow_le_rpow_of_nonpos` gives `f x ^ (-s) ≤ (2 ^ n) ^ (-s)`, and
   `(2 ^ n) ^ (-s) = 2 ^ s * r ^ (n + 1)` by the `rpow` exponent laws. Hence
   `ofReal (f x ^ (-s)) ≤ g (n + 1) x ≤ ∑' k, g k x`.
2. *Integrate.* By `lintegral_mono`, `lintegral_tsum` (each `g k` is measurable) and
   `lintegral_indicator_const`, the integral is at most
   `∑' k, ofReal (2 ^ s) * ofReal r ^ k * ν (S k)`.
3. *Volumes.* `hV` at `R = 2 ^ k ≥ 1` gives
   `ν (S k) ≤ ofReal (C * (2 ^ k) ^ D) = ofReal C * ofReal (2 ^ D) ^ k`. So the `k`-th term is at
   most `A * ρ ^ k` with `A = ofReal (2 ^ s) * ofReal C` and
   `ρ = ofReal r * ofReal (2 ^ D)`.
4. *Geometric series.* `ρ = ofReal (2 ^ (D - s)) < 1`, because `D - s < 0`
   (`Real.rpow_lt_one_of_one_lt_of_neg`). By `ENNReal.tsum_mul_left` and
   `tsum_geometric_lt_top`, `∑' k, A * ρ ^ k = A * ∑' k, ρ ^ k < ⊤`.

**`integrable_rpow_neg`.** `x ↦ f x ^ (-s)` is measurable (`Measurable.pow_const`) and
nonnegative (`Real.rpow_nonneg`, as `f x ≥ 1 > 0`), so `hasFiniteIntegral_iff_ofReal` reduces
finiteness to the dyadic bound.

**`integrable_of_norm_le`.** `K * f ^ (-s)` is integrable (`Integrable.const_mul`), and
`Integrable.mono'` gives integrability of `φ`.

**`continuous_rationalMatrixNorm`.** By definition the height is the maximum of
`entryNorm (ρ(g))` and `entryNorm (ρ(g)⁻¹)`, and `ρ(g)⁻¹ = ρ(g⁻¹)` (`map_inv`). Each entry of
`ρ(g)` is continuous in `g` (public `continuous_rationalMatrix_entry`), inversion is continuous
on `G(F)`, and the absolute value is continuous (public
`continuous_residueNormalizedAbsoluteValue`). Public `continuous_entryNorm_comp` (module
`OppositeUnipotentDisplacement`) turns entrywise continuity of absolute values into continuity
of `entryNorm`, and `Continuous.max` finishes.

**Local-field theorems.** `exists_hasPolynomialSublevelVolume_rationalMatrixNorm` is the public
`exists_measure_rationalMatrixNorm_le_mul_pow` restated with the definition. For the main
theorem, take its `D`. The weight `x ↦ rationalMatrixNorm F ρ₀ x` on `H` is continuous, as the
composite of `continuous_rationalMatrixNorm` with the inclusion `H → G(F)`, hence measurable for
the Borel structure on `H`. It is at least `1` by `one_le_rationalMatrixNorm`. Apply
`integrable_rpow_neg`.

## Scope

The exponent `D` comes from the volume bound and is not explicit; it is not related here to
roots, to the modulus character or to the dimension of `H`. Integrability is proved only for
negative real powers of the height, `s > D`, and functions dominated by a multiple of one of
them. The theorems need `H` to be closed and normalized by all of `χ(Fˣ)`; they do not show that
a given subgroup has these properties. Nothing here bounds an intertwining integrand by a power
of the height, identifies quotient measures, or concerns the host conditional intertwining
theorem.
