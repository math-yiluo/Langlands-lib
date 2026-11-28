# Blow-ups with a chart at a global section of the centre: proof

`Langlands.AlgebraicGeometry.blowupChartStatement` proves the Library proposition
`Langlands.AlgebraicGeometry.BlowupChartStatement` (module
`Langlands.AlgebraicGeometry.BlowupChartStatement`).

```lean
theorem blowupChartStatement : BlowupChartStatement.{u}
```

## Proof

The blow-up is `Scheme.IdealSheafData.blowup` of the pinned `weil-conjectures` package
(`WeilConjectures.Blowup`), with structure map `blowupMap`. The package supplies its properness
(module `WeilConjectures.Blowup.Proper`), the isomorphism over the complement of the support of the
ideal (`isIso_blowupMap_restrict_support_compl`, module `WeilConjectures.Blowup.Complement`), and,
for an affine open `U` and a section `a` of the ideal over `U`, the open chart `blowupChart U` with
`blowupChart_comp_blowupMap` and the identification `AffineBlowup.homogeneousAwayEquivChart` of its
coordinate ring with the affine chart ring `AffineBlowup.chartRing`.

- `coordinateAlgebra_eq_chartRing`: the Library's dilatation algebra
  `Langlands.GroupScheme.Dilatation.coordinateAlgebra a I` (the `A`-subalgebra of `A[1/a]` generated
  by the quotients `f/a`, `f ∈ I`) equals `AffineBlowup.chartRing I a`.
- `blowupChartStatement`: the chart over `U` is the blow-up chart precomposed with the isomorphism
  `Spec A[I/a] ≅ Spec (chart ring)`; the compatibility of the structure maps is
  `AffineBlowup.homogeneousAwayToChart_awayAlgebraMap`.

The theorem depends only on the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

Source: The Stacks Project, Sections 10.70 and 31.33 (Lemmas 31.33.2, 31.33.4 and 31.33.13), as
cited in the Markdown of `BlowupChartStatement`.
