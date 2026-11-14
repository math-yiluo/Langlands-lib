# Points of the Grassmannian are determined by their pullbacks of the universal divisor

Authors: Worker 5705.

Helper module of the proof of `Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralLinearSystemStatement` (entry module `Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralLinearSystemProof`), written for Task 5705. It contains no `sorry` and no new axioms.

## Content

Namespace `Langlands.AlgebraicGeometry.Picard.LinearSystemCechModule`.

- `homEquivSections_smul`: `σ_{b • v} = b • σ_v` (the `B`-action through `Γ(X_B, ⊤)`).
- `bijective_algebraMap_top`, `exists_isUnit_algebraMap_eq` (`R` noetherian, `π` proper, flat,
  geometrically integral): `B → Γ(X_B, 𝒪)` is bijective (FLT
  `bijective_app_of_isProper_of_flat_of_geometricallyReduced_of_geometricallyConnected`, with
  geometric connectedness from the Library's `geometricallyConnected_of_geometricallyIntegral`), so
  units of `Γ(X_B, 𝒪)` come from units of `B`.
- `linePt_congr`, `ptOf_eq_linePt`.
- `eq_of_comap_eq_of_inSomeChart` (`B` noetherian): two chart `B`-points with the same pullback of
  the universal divisor are equal. Their zero loci are those of regular sections `σ_{v₁}`,
  `σ_{v₂}`, which differ by a unit of `Γ(X_B, 𝒪) = B`
  (`SectionZeroIdeal.exists_isUnit_eq_smul_of_zeroIdeal_eq`), so `v₂ = c v₁` and both points are
  the same line quotient.
- `eq_of_comap_mapX_eq`: the same for points over any locally noetherian test scheme, by covering
  it with affine opens on which both points land in charts.

## Source

Kleiman, *The Picard scheme*, p.25 (proof of Theorem 3.13): the pair `(N, u)` attached to a
divisor is determined up to isomorphism, using `𝒪_T = f_{T*}𝒪_{X_T}` (Exercise 3.11).
