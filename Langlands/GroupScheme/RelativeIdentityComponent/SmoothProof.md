# Smooth relative identity-component structure

`Langlands.GroupScheme.RelativeIdentityComponent.smoothStructure` proves the
published `SmoothStructureStatement.{u}` in every universe `u`. For every
scheme `S` and actual smooth group scheme `G : Grp (Over S)`, it gives an
actual open subgroup representing `IsRelativeIdentityComponent G i`, whose
structure morphism is smooth and geometrically connected. Every supplied
representative is normal on all test schemes, including nonreduced and
nonaffine tests, and remains a representative after every actual base change.

The implemented proof applies `smoothStructure_of_openness` from
`SmoothReduction` to the proved theorem
`Langlands.AlgebraicGeometry.SectionComponent.flatFinitePresentationOpenness`
from `SectionComponentOpennessProof`. The latter proves the generic
flat finite-presentation section-component openness proposition with all
its morphism hypotheses. Its Noetherian approximation argument retains
arbitrary bases. The reduction applies this result on affine neighbourhoods
of the unit section, where the requisite finiteness conditions hold; global
quasi-compactness or quasi-separatedness of the group is not required.

In that reduction, the resulting open unit neighbourhood lies inside the
relative identity set and contains the whole unit section. Its two-factor
multiplication image is open because the restricted multiplication map is
smooth. Pullback image comparisons and `FieldProductCover` show that this
image contains every residue-fibre identity component. Multiplication closure
gives the reverse containment, so the relative identity set is open.

`OpenConstruction` equips the actual open restriction with the restricted
group operations and proves its all-test representation criterion.
`OpenGeometry` proves geometric connectedness by identifying its actual
residue fibres with the pointed smooth field identity components.
`RelativeIdentityComponentProperties` proves normality and uniqueness of
representatives. `BaseChange` uses actual Cartesian residue-fibre comparisons
and geometric connectedness to prove the representation criterion after
arbitrary base change; uniqueness transfers this conclusion to every supplied
representative. These are the three conjuncts assembled by the reduction.

This final proof is an internal composition of those Library results. Its
source target and conventions are documented in
`RelativeIdentityComponentStatements`: SGA 3, Exposé VI_B, Definition 3.1,
Proposition 3.3 and Theorem 3.10, in the registered Gille–Polo edition.
The generic openness input and its EGA provenance are documented in
`SectionComponentOpennessProof`. No additional literature assertion or final
premise is introduced here. The original proposition and its imports are
unchanged. The arbitrary universe, base schemes, test schemes and base-change
morphisms remain unrestricted.
