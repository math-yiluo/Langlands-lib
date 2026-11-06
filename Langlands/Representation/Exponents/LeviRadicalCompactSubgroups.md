# The rational points of a unipotent radical are a limit of compact subgroups

Author: Worker 16, as a helper for task `27fe1be6-a9cb-4bc5-8f71-3af15cd3d92b`
(Renard VI.1.2 and VI.1.3 for represented parabolics). Module
`Langlands.Representation.Exponents.LeviRadicalCompactSubgroups`, namespace
`Langlands.Aubert.General.RepresentedParabolic`.

## Provenance

Internal. These two theorems supply, for every actual parabolic, the structural input on the
unipotent radical that the published abstract normalized functors need. They require no root
presentation and no dynamic description of the radical.

## Setting

`k` is a nonarchimedean local field (`[Field k] [ValuativeRel k] [TopologicalSpace k]
[IsNonarchimedeanLocalField k]`). `G`, `P` and `U` are group schemes over `Spec k` with
`[IsAffineHom G.X.hom]`. The module installs a local instance `radicalPointTopology`: the
canonical topology `RationalPointFamily.pointTopology` on `rationalPoints G`, which is the one
the represented-parabolic statements install.

## Theorems

`isLimitOfCompactSubgroups_pointImage_radical` takes `p : P ⟶ G` with
`IsClosedSubgroup p` and `r : U ⟶ P` with `IsUnipotentRadical r`. It proves
`Jacquet.Localization.IsLimitOfCompactSubgroups (pointImage (r ≫ p))`: every compact subset
of the literal image of `U(k)` in `G(k)` lies in a compact subgroup of that image. Proof:
`G.X.left` is affine (`isAffine_of_isAffineHom`) and `U` is smooth (`hr.smooth`), hence
locally of finite type. The composite `r ≫ p` is a closed subgroup
(`hr.isClosedSubgroup.comp hp`) and `U` is unipotent (`hr.isUnipotent`). Apply
`exists_isCompact_subgroup_superset_range_of_isUnipotent` (module
`Langlands.GroupScheme.Rational.UnipotentCompactSubgroups`). Since `pointImage (r ≫ p)` is
by definition `(rationalPoints.map (r ≫ p)).range`, this is the required statement.

`isUnimodularModulus_pointImage_radical` adds `[T2Space k]`,
`[LocallyCompactSpace (rationalPoints G)]` and `[NonarchimedeanGroup (rationalPoints G)]`.
Under the same hypotheses on `p` and `r` it proves
`IsUnimodularModulus (pointImage (r ≫ p)) (isClosed_pointImage_comp p r hp
hr.isClosedSubgroup)`: the Haar modulus of conjugation on the radical image is trivial on
the radical image itself. Proof: the published
`isUnimodularModulus_of_isLimitOfCompactSubgroups` applied to the previous theorem.
