# Rational residue parabolics at a maximal Gamma-facet

This derived implication uses the original integer-valued KP quotient building,
its actual coefficient action, its full facets and its Gamma-facet maximality.
It has arbitrary universe and characteristic. All apartment, maximal split
torus, connected reductivity, centralizer and full-V6 inputs remain explicit;
an order-one unit supplies the published affine-root-system theorem.

A local domain with the upstairs field as fraction field, actual facet model
pairs and their actual generic-identity comparisons are supplied. At the
Gamma-facet a specified actual reductive quotient is identified with the base
change of a connected reductive group over a ground residue field. A specified
homomorphism from the original coefficient automorphisms to the residue-field
automorphisms and the all-test coefficient compatibility remain inputs.
The facet-parabolic bijection is also an explicit geometric premise. This
module constructs none of these objects or missing geometric premises.

`residueFacetImage` transports the actual special-fibre schematic image through
the supplied quotient isomorphism. `HasGaloisResidueImageCompatibility` says
that this original incident-facet map intertwines the published coefficient
action with canonical subgroup-functor Galois transport. It is a compatibility
condition on the actual maps, rather than a new action on replacement facets.

For a ground-residue parabolic, the published arbitrary-field extension theorem
makes its base change parabolic, and ambient isomorphism transport puts it in
the actual quotient. Surjectivity of the supplied facet-parabolic bijection
selects its incident full facet. A subgroup functor pulled back from the ground
field is fixed by canonical coefficient transport; compatibility and
injectivity therefore make this incident facet fixed. The published maximality
criterion identifies it with the original Gamma-facet. The proved self-image
normalization in `IntegerFacetParabolicImages` then makes the extended parabolic
all of the residue group on every test scheme. Monicity makes the extended
inclusion an isomorphism, and fpqc reflection along the residue-field extension
makes the original parabolic inclusion an isomorphism.

The final corollary applies the published
`IsMaximalSplitTorus.exists_commFactor_of_noProperParabolic`. Thus any prescribed
maximal split torus of the downstairs residue group is central and factors
through every maximal torus, with the same source torus and a maximal split
factor. This uses an existing algebraic theorem rather than constructing a
valuation-ring torus lift or a segment model.

`GaloisFacetResidueParabolicsStatement` records both conclusions, conditional on
the order-one unit, maximality and each of the supplied residue-group and
geometric premises. `galoisFacetResidueParabolics` assembles their proofs.

The provenance is internal: the proof composes the actual incidence maximality
criterion, special-fibre self-image normalization, arbitrary-field parabolic
extension and ambient transport, canonical descent transport, and fpqc
isomorphism reflection. The geometric bijection, quotient descent comparison
and coefficient compatibility still require construction before this result
can contribute to an unconditional prescribed-point split-torus proof.
