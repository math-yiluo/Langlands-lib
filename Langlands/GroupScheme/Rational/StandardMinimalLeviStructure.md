# Canonical minimal standard Levi and geometric radical

Author: Worker 1623.

`Langlands.GroupScheme.StandardMinimalLeviStructureStatement.{u}` records
three structural conclusions for the existing canonical empty-index
standard subgroups. For every field `k : Type u`, connected reductive
group scheme `G` over `Spec k` with the affine interface, maximal split
torus `i : T → G`, and generic cocharacter `ν` of `T`, it asserts that:

- `Standard.leviScheme i ν ∅` is connected reductive.
- The actual map `Standard.leviToParabolic i ν ∅` is a rational Levi
  subgroup in the existing `IsRationalLeviSubgroup` sense.
- The actual map `Standard.unipotentToParabolic i ν ∅` satisfies
  `LeviSubgroup.IsGeometricUnipotentRadical`, so it is the radical over the
  ground field and after extension to the algebraic closure.

`standardMinimalLeviStructure` derives this proposition from published
Library results. All three conclusions concern the original canonical
representatives and their actual inclusion maps. The result has arbitrary
universe and field scope, including nonsplit groups and empty relative
root systems. It assumes neither reductivity of the Levi nor a radical
identification, and has no `StandardCocharacterStatement` premise.

## Implemented derivation

`Standard.isConnectedReductive_emptyLevi` uses the published equality
`standardLevi_empty_eq_dynamic_of_generic` to make the canonical closed
Levi inclusion a representative of the actual dynamic centralizer of
`CommGroupScheme.groupHom ν ≫ i`. The published
`dynamicCentralizerReductive` then proves connected reductivity of this
representative.

`Standard.isGeometricUnipotentRadical_empty` also uses
`standardParabolic_empty_eq_dynamic_of_generic` and
`standardUnipotent_empty_eq_dynamic`. These equalities identify the
canonical parabolic and unipotent functors on every test scheme.
`Standard.unipotentToParabolic_comp` identifies the composite of the
actual unipotent-to-parabolic inclusion with the ambient inclusion.
The published
`Dynamic.isGeometricUnipotentRadical_of_centralizer` applies to these
representatives and the newly established reductive canonical Levi.
Its conclusion is the full geometric radical predicate of
`Rational.SemistandardIntersection`, including greatestness over the
algebraic closure among all smooth connected normal unipotent closed
subgroups. No descent premise on these subgroups is imposed.

The canonical parabolic is affine because it is closed in the affine
ambient group. The existing affine radical comparison therefore turns
this conclusion into `LeviSubgroup.IsGeometricUnipotentRadical` in
`Standard.isLeviGeometricUnipotentRadical_empty`. This step uses the
published preservation of unipotence under field extension, as
implemented in `Rational.AffineGeometricUnipotentRadical`.

For `Standard.isRationalLeviSubgroup_empty`, closedness of the actual
Levi-to-parabolic inclusion follows from its closed ambient composite
and closedness of the parabolic inclusion. The existing
`IsRationalLeviSubgroup.of_geometricUnipotentRadical` combines this,
Levi reductivity, the geometric radical, and the published
`Standard.isIso_emptySubgroupMultiplication`. Thus its multiplication
witness is the existing canonical Levi-first scheme multiplication.

The final theorem collects these three conclusions. The comparisons
used here retain the supplied generic cocharacter and maximal split
torus; all subgroup equalities are on arbitrary test schemes, including
nonreduced tests.

## Provenance and remaining obligations

This is an internal composition of published Library definitions,
comparisons and proofs, rather than a new translation of an external
source assertion. Their source provenance remains documented in the
imported modules. In particular, this unit specializes the existing
dynamic radical reduction to the canonical standard representatives and
uses the published centralizer theorem to discharge its reductivity
premise. It does not submit a duplicate proof of the independently owned
universal `DynamicGeometricUnipotentRadicalStatement`.

This unit supplies the rational Levi and geometric unipotent radical
clauses of `IsSiegelAlgebraicSetup` once a maximal split torus and generic
cocharacter have been chosen. It supplies no minimal-parabolic existence
or minimality, derived/central split-torus product, compact subgroup,
Iwasawa decomposition or rational-left adelic coverage. The full
`AdelicGoodSiegelReductionStatement` remains a separate proof obligation.
