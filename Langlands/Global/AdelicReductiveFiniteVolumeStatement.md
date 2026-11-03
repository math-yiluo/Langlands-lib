# Finite volume of the norm-one adelic rational quotient of a connected reductive group

`Langlands.Global.AdelicGroupPoints.ConnectedReductiveFiniteVolumeStatement` is a Prop-valued
target for the finite-volume assertion of Getz–Hahn, *An Introduction to Automorphic
Representations* (2024), §2.6, Theorem 2.6.3, printed p.69, restricted to connected reductive
groups over number fields (Borel–Harish-Chandra). The module states it and does not prove it.

## Statement

The proposition quantifies over every number field `F : Type u` and every group scheme `G`
over `Spec F` with instances `IsAffine G.X.left` and `LocallyOfFiniteType G.X.hom`. If
`IsConnectedReductive G` holds (Library definition in `Langlands.GroupScheme.Reductive.Basic`:
smooth, affine, connected, with trivial unipotent radical after base change to an algebraic
closure), then `normOneRationalQuotientHaarMeasure F G` is a finite measure.

The measure is the existing one from `Langlands.Global.AdelicGroupHaarMeasure`: on
`G(F) \ G(𝔸_F)¹`, the quotient of the fixed `Measure.haar` on the norm-one adelic group by
counting measure on the principal subgroup. The conventions are those of the general target
`NormOneRationalQuotientFiniteVolumeStatement` (see its Markdown). This statement adds
reductivity and keeps the rest unchanged. It asserts no Siegel-set covering, no compactness
criterion and no comparison with `A_G G(F) \ G(𝔸_F)`.

## Relation to the general target

`connectedReductiveFiniteVolumeStatement_of_normOne` proves that the general target implies
this statement. It applies the general statement with the smoothness and connectedness fields
of `IsConnectedReductive`. The intended use goes the other way. Together with the Levi
decomposition statement (`Langlands.GroupScheme.CharacteristicZeroLeviDecompositionStatement`),
compactness of the rational quotient of a unipotent group, and
`LeviReductionFiniteVolumeStatement`, this reductive case is meant to give the general target.

## Source

Getz–Hahn, Theorem 2.6.3 (Borel, Conrad, Harder, Oesterlé), printed p.69 (PDF p.86): if `G`
is smooth and connected, `G(F) \ G(𝔸_F)¹` has finite volume. Here `G(𝔸_F)¹` is defined by
(2.19), printed p.68, as the intersection of the kernels of `|χ|` over `F`-rational characters
`χ`. The measure is induced by Haar measure on `G(𝔸_F)¹` (printed p.69, before the theorem,
and §3.6). A connected reductive group is smooth and connected, so this statement is the
reductive special case of the theorem, over number fields. Getz–Hahn attribute the
finite-volume assertion to Conrad [Con12a, Theorem 1.3.6]. This file cites the Getz–Hahn
statement and does not claim a reading of Conrad. The October 2026 author errata, all five
pages read, have no Chapter 2 entry, so they change neither (2.19) nor Theorem 2.6.3.

Source records: `getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`, §2.6, (2.19) and
Theorem 2.6.3, printed pp.68–69 (PDF pp.85–86); `getz-hahn-2024-errata-2026-10`, SHA-256
`e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`, all five pages.
