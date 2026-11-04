# Empty torus roots and geometric nilpotence

This internal supporting unit proves `EmptyRootsNilpotenceStatement.{u}`:
over any algebraically closed field `k : Type u`, a smooth connected affine
group whose actual maximal torus has empty adjoint root support is
geometrically nilpotent. The maximal torus is an actual closed subgroup.
Geometric nilpotence has the existing meaning of nilpotence of the group of
points over the algebraic closure.

The first two helpers work over arbitrary fields. The internal direct-sum
decomposition into split-torus Lie weight spaces implies that the zero
weight space is the whole Lie algebra if the root support is empty: every
nonzero character then has zero weight space. The differential of the
conjugation action consequently fixes every Lie vector over all coefficient
algebras. The published rigidity theorem for diagonalizable actions on
smooth connected affine groups makes its entire fixed subgroup the whole
group. The fixed subgroup is the all-refinement torus centralizer, so the
original torus map is central on every scheme test. This part requires
neither maximality nor an embedding of the acting split torus.

For an actual central maximal torus over an algebraically closed field,
`IsMaximalTorus.centralQuotient` supplies a smooth connected affine quotient
with no nontrivial homomorphisms from any torus. In particular, every
cocharacter is zero. The previously proved
`AbsoluteNoCocharacter.isUnipotent` theorem therefore makes this quotient
unipotent. Its actual kernel is central. The existing central-extension
theorem supplies a finite lower-central-series bound on all scheme tests of
the original group, including nonreduced tests, and this implies geometric
nilpotence.

Finally, finite Galois splitting makes the chosen maximal torus split over
the algebraically closed base. The centrality criterion above then applies
to its empty root support, proving the packaged proposition.

All results here are internal consequences of the imported Library
theorems. Although `Cartan.CentralTorusQuotient` also contains a separate
conditional theorem using `NoTorusUnipotentStatement`, this proof uses only
its actual quotient construction and central-kernel and uniform-bound
helpers. It invokes the already proved algebraically closed no-cocharacter
criterion. It does not assume or prove the arbitrary-field no-torus
unipotence statement, the isogeny reduction, or termination of weight
descent.
