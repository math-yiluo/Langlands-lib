# The scheme of ordered torsion tuples in a supplied family

This internal construction uses the actual finite product, in schemes over
`S`, of `2*g` copies of the multiplication-by-`n` kernel of a supplied
abelian scheme `A`. Maps from every actual `T : Over S` into
`torsionTupleScheme A g n` correspond to ordered tuples of actual torsion
points `Level A.toGrp T n`. The inverse takes the product lift of the
actual kernel points supplied by `kernelLevelEquiv`. The product
projection equations and the inverse laws of that equivalence prove the
two inverse identities. Precomposition of actual morphisms corresponds
to the published restriction map on torsion points.

`sectionTupleBaseChangeEquiv` uses the existing actual torsion base-change
linear equivalence, including its identity-test comparison, to identify
such tuples at a base map `b` with the unchanged `SectionTuple` on the
actual base-changed abelian scheme. Composing the equivalences gives
`torsionTupleSectionEquiv`, with all scheme maps and no noetherianity,
positivity, invertibility, dimension or rank hypothesis.

`tautologicalTorsionTuple` decodes the identity morphism of the parameter
scheme. Its coordinates, under the actual base-change comparison, are
exactly the product projections interpreted as actual kernel points.

The provenance is internal: the construction combines the categorical
finite product with the published actual multiplication kernel, torsion
point equivalence and base-change equivalence. It parameterizes all
ordered torsion tuples in one supplied family. No fullness, existence of
full levels, moduli space or automorphism rigidity is asserted.
