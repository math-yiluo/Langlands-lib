# Splitting a Siegel set over the band

Module: `Langlands.Automorphic.CuspidalAdmissible.Split`. Provenance: internal; the usual
decomposition of a Siegel set into a compact part and neighbourhoods of the cusps.

- `compactRegion Q₁ B = {torInf(x) · q : |x_i| ≤ B, q ∈ Q₁}` (archimedean torus element with
  logarithmic coordinates `x` times an element of `Q₁`); `isCompact_compactRegion` for compact
  `Q₁`.
- `absDet_eq_determinantNorm`: the Library's `absDet` is the determinant norm.
- `exists_siegel_band_split hQ₁ hK hform`: suppose every element of the Siegel set
  `siegelSetGL ΩN C c` is `torInf(x) · q` with `q ∈ Q₁` (compact) and `x` in the chamber with
  constant `K ≥ 0` (`hform`, supplied by `exists_torus_form`). Then there is `R` such that for
  every `T ≥ 0`, every element of the Siegel set lying over the band either lies in
  `compactRegion Q₁ (R + n(n(K + T)))` or lies in `cuspRegion ΩN C c Q₁ K a T` for some block
  position `a > 0` (module `CuspRealization`).

  Proof: `|log |det q||` is bounded by `L₁` on `Q₁`; over the band `1 < |det| < 2`, so
  `|∑ x_i| ≤ log 2 + L₁` (`abs_sum_le_of_absDet`). If every consecutive drop of `x` is at most
  `T`, the chamber condition bounds all differences `x_i - x_j` (`sub_le_of_chamber`) and then
  each `|x_i|` (`abs_le_of_sub_le`); otherwise some drop at a position `a > 0` exceeds `T`.
