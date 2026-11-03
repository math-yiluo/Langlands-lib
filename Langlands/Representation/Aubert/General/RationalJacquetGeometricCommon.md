# Actual geometric Jacquet terms from point-source intersection identities

This internal reduction connects actual geometric terms to the common map used
by the finite Jacquet assembly. It keeps the supplied Coxeter system on the
actual point Weyl quotient, with the same simple-root labels. The remaining
subgroup geometry is an explicit hypothesis; the module does not prove those
structural identities or the full rational Aubert compatibility statement.

`PointSourceIntersectionIdentities` states three subgroup equalities for every
minimum representative `w` for `I,J` and every actual normalizer lift `n`.
The actual source Levi intersection is the standard Levi at
`simpleImage cs w⁻¹ I ∩ J`. Inside the literal ambient Levi `M_J`, the actual
source parabolic and radical equal the corresponding literal standard
restricted parabolic and radical. The predicate contains no functor comparison,
Grothendieck-group identity, preservation premise or scheme Coxeter realization.

`pointTargetIntersectionIdentities` applies the source predicate to `J,I,w⁻¹`
and `n⁻¹`. Minimum-representative inversion and the quotient homomorphism supply
the hypotheses. Expanding the actual source and target intersections gives the
target identities at `simpleImage cs w J ∩ I`.

`geometricIntersectionDecompositions_of_pointSource` reindexes both finite
intersections by their subtypes in the two coarse labels. The literal standard
semidirect decompositions inside the Levis then transport to both actual
geometric decompositions. `geometricTermFiniteLength_of_pointSource` uses the
same subgroup equalities and the generic preservation reduction to derive
finite-length and finite-length short-exact preservation of the actual source
Jacquet and target induction functors. Its actual decomposition witnesses may
be arbitrary.

`geometricTermK0_eq_intersection_of_pointSource` uses the generic
`geometricTermK0_eq_standardOfEq` comparison to identify every actual geometric
term for `r_J i_I` with `rationalRestrictedJacquetTerm`. The source fine subtype
is `simpleImage cs w⁻¹ J ∩ I` inside `I`, and the target fine subtype is
`simpleImage cs w I ∩ J` inside `J`. Fine-Levi inverse-conjugation membership is
derived from the point root-length and positive-simple-reflection comparisons,
minimum-representative support, and the standard Levi-conjugation statement.
The preservation witness for the actual geometric term may be arbitrary.

`geometricTermK0_comp_ambient_eq_common_of_pointSource` composes this equality
with ambient source Jacquet restriction and uses the proved standard-term
comparison from `RationalJacquetTermCommon`. Thus source stages and finite
reindexing, including the actual Haar-character factorization derived from
continuous standard projections, give the common term at
`w, simpleImage cs w I ∩ J`.
`jacquetGeometricTermReduction_of_pointSource` packages the result as precisely
the common-term premise of the generic finite Jacquet assembly. Its geometric
decompositions and actual preservation witnesses may be any witnesses of the
specified properties.

The field and representation universes remain independent, with carrier
universe `max (u + 1) v`. The ambient topology is the actual point topology.
Local compactness, nonarchimedeanness, closed radicals and Levis, the standard
Levi-intersection and standard-cocharacter statements, actual ambient and
restricted finite-length and short-exact preservation, continuous ambient
standard projections and compact-limit decomposition of the literal restricted
radicals remain explicit where used.

The provenance is internal composition of actual subgroup-equality transport,
normalizer inversion, the generic geometric-term reduction, and the proved
rational source-stage and common-term comparisons. No structural identity is
silently added to the final compatibility target. Proving
`PointSourceIntersectionIdentities` at the target's weaker point-Coxeter scope,
the geometric expansion and the longest-survivor comparison remain separate
obligations.
