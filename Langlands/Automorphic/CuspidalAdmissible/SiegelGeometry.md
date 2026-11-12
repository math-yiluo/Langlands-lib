# Geometry of the actual adelic Siegel sets

Module: `Langlands.Automorphic.CuspidalAdmissible.SiegelGeometry` (namespace
`Langlands.Global`). Provenance: internal; elementary facts about the Library's Siegel sets
`PrimitiveAdelicHeight.siegelSetGL` used for integral estimates.

- `exists_siegel_data F n ΩN C c ...`: for compact unitriangular `Ω_N`, compact `C` and
  `c > 0` there are a compact `Q₁` and `K ≥ 0` such that every `h` in the Siegel set is
  `Ngl * diagonalGL ω * A_x * κ`, where `Ngl` is an invertible matrix with value in `Ω_N`,
  `ω i ∈ C`, `κ` is in the standard compact subgroup, `A_x = ofInfinite (torInf x)` with `x`
  in the chamber `Chamber K x` (consecutive rises at most `K`), and `A_x⁻¹ * h ∈ Q₁`. The
  proof is the Library's argument inside `exists_siegelDecomposition`, applied to a Siegel
  point directly: `x = log r`, the chamber bound `max 0 (log c / [F : ℚ])` from the Siegel
  ratio condition, and `A_x⁻¹ h = (A_x⁻¹ N A_x) · diag(ω) · κ` lies in
  `entryBox(E) · diag(C^n) · K_std`, because torus conjugation of an upper triangular matrix
  (and of its adjugate) stays bounded in the chamber (`conj_apply_mem`).
- `exists_torus_form F n ΩN C c ...`: consequently every `h` in the Siegel set is
  `ofInfinite (torInf x) * q` with `q ∈ Q₁` and `x` in the chamber.
- `finite_rational_compact`: only finitely many rational `γ` satisfy `γ g ∈ K₂` for some
  `g ∈ K₁` (`K₁`, `K₂` compact): `rational γ ∈ K₂ K₁⁻¹`, whose matrix entries lie in compact
  sets meeting the discrete closed principal adeles in finite sets.
- `encard_rational_mul_mem_le S x`: the number of rational `γ` with `γ x ∈ S` is at most the
  number of `γ` with `γ S ∩ S ≠ ∅` (translate by a fixed `γ₀`).
- `detOneGL`, `siegelRatioSet` (closed chamber condition in logarithmic coordinates,
  `|a(expUnit x)| = exp(x)^d` by `absoluteValue_full_expUnit`), `siegelParamMap` (continuous,
  `continuous_siegelParamMap`), `range_siegelParamMap`: the Siegel set is the image of
  `Ω_N × C^n × siegelRatioSet × standardCompact`.
- `measurableSet_siegelSetGL`: Siegel sets are Borel, being continuous images of a
  σ-compact space in a Hausdorff group.
- `mul_mem_siegelSetGL`, `isCompact_mul_image`, `isUnitriangular_mul_image`: left
  multiplication by elements of a set `U` replaces `Ω_N` by `U · Ω_N`, which is compact and
  unitriangular when `U` is.
