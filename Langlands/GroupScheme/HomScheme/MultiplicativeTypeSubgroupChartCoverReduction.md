# Finite-type reduction for multiplicative-type subgroup charts

Author: Worker 872.

`MultiplicativeTypeSubgroupModuli.chartCoverReduction.{u}` proves
`ChartCoverReductionStatement.{u}`: chart covers over spectra of
finite-type integer algebras suffice for chart covers over every
scheme. The finite-type chart-cover proposition remains an explicit
input. There is no assumption that the arbitrary base be affine,
Noetherian or quasi-compact.

For `G` over an affine base `Spec R`, the published
`TorusSubgroupModuli.exists_finiteType_model` theorem supplies a
smooth affine model `G₀` over a ring `R₀` of finite type over `ℤ`,
together with an actual isomorphism from `G` to its base change.
Apply the chart-cover input to `G₀`, pull those charts back to `R`,
and transport them through the ambient isomorphism.

For an arbitrary base, restrict `G` to every affine open using
`IsAffineOpen.fromSpec`. Each restriction is smooth and affine by
base change and has a chart cover by the affine argument. The
open-extension theorem combines these into charts over the original
base, with coverage of every field point.

The final theorem
`multiplicativeTypeEtaleLift_of_finiteTypeCharts` composes this
reduction with the published-input conditional chart-lifting
construction in the companion module. It proves the unchanged
`MultiplicativeTypeEtaleLiftStatement` under the sole explicit
`FiniteTypeChartCoverStatement` input. No instance of that input is
proved here, so this is not an unconditional lifting proof.

The reduction follows the noetherian step of SGA 3, Exposé XI,
proof of Theorem 4.1, registered source
`sga3-exposes-xi-xii-xiv-gille-polo-2008`, `Expo11.pdf`, PDF p.21,
recomposed p.105, original p.159. It adapts the published torus
chart-cover reduction using the generic smooth-affine finite-type
model theorem and the multiplicative-type chart transport lemmas.
