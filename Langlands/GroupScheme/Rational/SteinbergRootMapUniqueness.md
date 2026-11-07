# Uniqueness of supplied normalized simple-root parametrizations

Worker 1317. Provenance: internal, derived from the published all-test root,
weight-coordinate and Lie-rigidity interfaces. The definitions and lemmas below
support the split Steinberg quotient proof; they do not establish that statement.

Both supplied maps represent the whole same root subgroup, so their represented
subgroup comparison is an actual automorphism of the standard additive line.
Their torus laws make the comparison equivariant for the nonzero simple-root
weight of the supplied split torus. Existing uniqueness of the scalar structure
of weight coordinates implies linearity on every scheme test. Normalization of
the two differentials fixes the standard epsilon vector, which spans the actual
Lie algebra of the additive line. Existing scalar-linear Lie rigidity then
makes the comparison the identity. Thus the parametrizations, and their ordered
Steinberg products with a fixed ordering and representatives, agree.

The proof retains arbitrary fields, including finite and imperfect fields of
positive characteristic. It asserts uniqueness, without existence. It does not
compare different reflection representatives or construct fundamental characters.

The entry definition
`SplitPinning.NormalizedRootParametrization.comparisonIso` is the isomorphism
supplied by `SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy`.
`comparisonIso_hom_comp` records its ambient compatibility.
`weightAction_comp` translates the supplied scalar-point conjugation identity
to every test point, and `comparisonIso_equivariant` cancels the represented
subgroup monomorphism. `comparisonIso_targetMap_eq_self` uses the pinning's
specified derivative and the one-dimensional vector Lie coordinates.
`hom_eq` applies
`RelativeRoot.isCoordinateLinear_of_weightCoordinates` and
`RelativeRoot.eq_id_of_coordinateLinear_of_targetMapLinear_eq_self`.
Proof irrelevance then gives the two subsingleton instances, and
`SplitPinning.steinbergProduct_eq_of_normalizedRootMaps` substitutes the equal
families in the actual ordered product.
