# Padding, transpose inverse and the determinant norm on actual adelic points

Provenance: internal. This module supports the proof of
`Langlands.Global.RankinSelbergGlobal.UnequalAnalyticStatement` (Cogdell 2004, Theorem 2.1).
It proves elementary facts about the maps `pad`, `iota`, `detNorm`, `detPower` and
`dualFunction` of `Langlands.Global.RankinSelberg.UnequalIntegrals`. These maps are defined on
the actual adelic points `Points F n` of the general linear group scheme by transport along
the Library comparison `GeneralLinearGroupPoints.adelicEquiv F n` (written `E n` below) with
the adelic matrix group `AdelicGL F n`. Each proof transports the corresponding matrix
statement along `E n`.

All declarations are in the namespace `Langlands.Global.RankinSelbergGlobal.UnequalAnalytic`.

## Matrix facts

- `continuous_padGL`: `M ↦ diag(M, I)` is continuous on `GL_m(R)` for a topological ring `R`.
  Each entry is an entry of `M` or a constant (`padGL_apply`), and the inverse is handled by
  `map_inv` and continuity of inversion (`Units.continuous_iff`).
- `inverseTranspose_padGL`: `ᵗdiag(M, I)⁻¹ = diag(ᵗM⁻¹, I)`, entrywise from `padGL_apply`.
- `inverseTranspose_map`: transpose inverse commutes with applying a ring homomorphism to the
  entries.

## Padding and transpose inverse on points

- `adelicEquiv_pad`: `E n (pad g) = padGL (E m g)`. `pad_mul`: `pad` is multiplicative.
  `pad_pad`: padding twice is padding once. `continuous_pad`: `pad` is continuous.
- `pad_rational`: the padding of a rational point is the rational point obtained by padding
  the rational matrix (Library `adelicEquiv_rational` and `padGL_map`).
- `adelicEquiv_iota`, `iota_iota` (involution), `iota_mul`, `continuous_iota`.
- `iotaEquiv F n`: `iota` as a topological group automorphism of `Points F n`
  (`adelicHomeomorph`, then `inverseTransposeContinuous`, then back), with
  `iotaEquiv_apply`.
- `iota_pad`: `ι (pad g) = pad (ι g)`. `iota_rational`: `ι` of a rational point is rational.
- `weylLong_eq_rational`: the long Weyl element of `GL_n(𝔸)` is the image of the long Weyl
  element of `GL_n(F)` (entries `0` and `1`).
- `dualFunction_eq`: if `φ` is left invariant under rational points, then
  `dualFunction F n φ g = φ (ι g)`. The dual function is `φ(w_n ᵗg⁻¹)`, and `w_n` is rational
  (`weylLong_eq_rational`). `dualFunction_iota`: `dualFunction F n φ (ι g) = φ g`.

## The determinant norm and its complex powers

- `detNorm_eq_absDet`: `detNorm F n g` is the Library `absDet F n (E n g)` (by definition).
  Hence `detNorm_pos`, `continuous_detNorm`, `detNorm_mul` and `detNorm_rational_mul` (the
  product formula, Library `absDet_rational_mul`).
- `determinant_padGL`, `detNorm_pad`: `|det diag(g, I)| = |det g|` (`det_padGL`).
- `determinant_inverseTranspose`, `detNorm_iota`: `|det ᵗg⁻¹| = |det g|⁻¹`
  (`Matrix.det_transpose`).
- `norm_detPower`: `‖detPower g s‖ = exp (Re s · log |det g|)`.
- `detPower_pad`, `detPower_rational_mul`, and `detPower_iota`:
  `detPower (ι g) s = detPower g (-s)` (`Real.log_inv`).
- `continuous_detPower`: `g ↦ detPower g s` is continuous (`|det g| > 0`).
