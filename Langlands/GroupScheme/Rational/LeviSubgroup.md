# Geometric radicals, rational Levi subgroups, and central subtori

Authors: Worker 1361 and Worker 1348.

This module supplies predicates for the geometric inputs in the proof of
`MinimalParabolicTorusSplitPartStatement`. It does not assert existence of a
radical, a Levi subgroup, or a largest central subtorus, and it does not prove
any parabolic structure theorem.

`IsSolvableRadical r` requires an actual closed subgroup morphism `r : R → P`,
with smooth, connected, solvable source and normal image on every test
scheme. Its image contains that of every smooth connected solvable normal
closed subgroup defined over the ground field. This is a ground-field
predicate, parallel to the published `IsUnipotentRadical`.

`IsGeometricSolvableRadical r` requires both `IsSolvableRadical r` and the
same property after base change to the algebraic closure. Similarly,
`LeviSubgroup.IsGeometricUnipotentRadical r` uses the existing `IsUnipotentRadical`
before and after that base change. In particular, the geometric predicates
do not identify a ground-field radical with a geometric radical by definition.
The additional base-change property is an explicit requirement. The
`LeviSubgroup` namespace distinguishes this conjunction from the existing
`IsGeometricUnipotentRadical` predicate in `Rational.SemistandardIntersection`;
the two definitions are retained separately.

For subgroup maps `l : L → P` and `r : U → P`,
`subgroupMultiplication l r` is the actual morphism of schemes over the
base `L × U → P` given by multiplication, with `L` first.
`comp_subgroupMultiplication` proves its evaluation formula on any test
scheme by the product projection identities and naturality of group
multiplication. No assertion that this map is a group homomorphism is made.

`IsRationalLeviSubgroup l` requires that `P` be affine, that `l` be closed, that `L` be connected
reductive, and that there exist a represented geometric unipotent radical
`r : U → P` such that `subgroupMultiplication l r` is an isomorphism of
schemes over the ground field. This is the connected version needed for
parabolics in a connected reductive group. The isomorphism requirement
retains the scheme structure in positive characteristic; a semidirect
product assertion on algebraically closed points would be insufficient.

`IsLargestCentralSubtorus z` requires an actual closed torus
`z : Z → L`, central on all test schemes, whose image contains every
actual closed central torus. Its universal property uses the existing
all-test subgroup functors. This characterizes the central torus needed
in the subsequent parabolic statements. This module does not construct
the reduced connected center or prove its comparison with this predicate.
In particular, it does not assert that the entire scheme-theoretic center
is a torus.

The source is Borel and Tits, *Groupes réductifs* (1965), registered as
`borel-tits-1965-groupes-reductifs`, SHA-256
`ec6674ba292deaadd77a449f4bad3750db79c0b87b117a892ef6b09bb16357ad`.
Section 0.7, printed p.59/PDF p.6, defines radicals as greatest connected
normal solvable or unipotent subgroups. Sections 0.6 and 0.8 on that page
define the semidirect-product condition by an isomorphism of varieties
and the Levi condition by a reductive complement to the unipotent radical;
0.6 expressly distinguishes this from the assertion on abstract groups.
The present predicates use smooth group schemes and an isomorphism over
the ground field, in the source's reduced algebraic-group convention
from 0.3, printed pp.57–58/PDF pp.4–5.

The central-torus interface is a derived universal-property formulation
motivated by 2.15(a),(e), printed p.70/PDF p.17, and 3.14, printed
p.80/PDF p.27. These passages identify the connected center of a
reductive Levi as the torus factor of the radical. The explicit
ground-field/geometric distinction and all-test universal properties are
implementation choices; no existence or descent result is imported as
an axiom. Worker 1348 contributed the geometric decomposition and scope;
Worker 1361 authored these interfaces and their documentation.
