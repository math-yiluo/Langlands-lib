# Haar conullness of the actual rational dynamic open cell

Author: Worker 200.

`RationalDynamicOpenCellConullStatement` is a focused unproved proposition
definition. It isolates the geometric-measure obligation needed to apply the
existing source open-cell integration theorem to actual reductive rational
points. Compilation establishes that the target is well formed; no proof,
conullness instance or completed rational-point integration formula is supplied.

## Actual objects and quantifiers

For every nonarchimedean local field `F` in an arbitrary universe, every actual
`GroupScheme G` over `Spec F` and `hG : IsConnectedReductive G`, use the existing
rational-point topology on `RationalPoint F G.X` and its Borel sigma algebra.
Affineness is obtained from the actual connected-reductive predicate for this
topology construction. No separate point-topology, countability or local
compactness hypothesis is inserted. This target is not restricted to
characteristic zero, split or quasisplit groups.

For each actual cocharacter `χ : Gm → G`, the parabolic subgroup `P` is the
actual carrier of `Dynamic.parabolic χ` on the identity test over `Spec F`.
The subgroup `V` is the actual carrier of `Dynamic.unipotent χ⁻¹`, where
`χ⁻¹` means precomposition with the existing power-minus-one map of `Gm`.
This is the source opposite radical for the dynamic parabolic. The map is
exactly the published `HarishChandraSchwartz.openCellMap`:
`(p,v) ↦ p v⁻¹` on these actual subgroup types.

The proposition asks, for every supplied left Haar measure `mu` on the actual
rational-point group, that the complement of this map's range have measure
zero. No arbitrary chart, model group, open cell, source scalar or exceptional
set is substituted. No right-invariance or normalization premise on `mu` is
needed for the null-set assertion. In particular, no compact subgroup or Haar
scale is selected to make the result hold.

## Proven prerequisite and remaining proof

The published `OpenCellPoints.isOpenEmbedding_openCellMap_rationalPoint`
already proves that this exact dynamic map is an open embedding when the
affine group is smooth. Both properties hold for the connected-reductive
setting of the target. This target asks only for the additional measure-zero
complement. It does not repackage the existing embedding theorem as a new
proof and does not infer conullness merely from openness or density.

The source context is Waldspurger, *La formule de Plancherel pour les groupes
p-adiques* (2003), I.1 (2), printed p.240/PDF p.6, and the normalization argument
on printed p.241/PDF p.7. Registered source `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
The paper states integration over the actual open cell. The present proposition
is an internal extracted prerequisite for the Library's implementation of
that formula; it is not a separately numbered source theorem. In the existing
`OpenCellIntegration` and `ParabolicHaar` engines it is precisely the `hnull`
premise. Together with the actual embedding theorem it will discharge the
geometric premises of `SemidirectSourceGamma` after the actual subgroup
identifications and remaining measure hypotheses are verified.

A proof successor must prove this exact target independently of the desired
open-cell integration formula or gamma identities whose realization uses it.
It must not assume an unproved general measure-zero algebraic-boundary or
analytic-chart theorem. Such substantial missing prerequisites need their
own independently published proofs. Existing open-cell and subgroup owners,
including operator-paused radical and root-product work, retain their scope
and run controls. GL-specific conullness results do not establish this general
target without a verified general comparison.

The statement alone closes none of the standing Plancherel completion
conditions. Source compact-intersection measures, all semistandard/opposite
comparisons, gamma dependence only on the Levi, root-factor index formulas,
spectral normalization and all representation/analysis conclusions remain
separate obligations.
