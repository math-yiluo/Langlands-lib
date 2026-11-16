# Weyl-normalized simple-root families over arbitrary local rings

This internal construction gives `simpleRootFamilyLocal` for an affine reductive
group over any commutative local ring, a closed fibrewise maximal coordinate
split torus, its fibrewise root datum and a base of that root datum. The family
is indexed by all roots. Its specified properties concern the simple roots
and their negatives: these maps are actual root parametrizations, and their
Weyl products act on the torus by the simple reflections. The theorem
`localSplitSimpleRootGroupLocal` proves precisely the published proposition
`LocalSplitSimpleRootGroupLocalStatement`, the first input of the local
Isomorphism Theorem assembly.

The proof first chooses an actual parametrization for every root using the
flat primitive-coordinate construction
`LocalRootGroup.exists_rootParametrization_of_flat`. For each simple root it
uses `exists_unit_weylNormalization` to rescale the opposite parametrization
by a unit. Unit rescaling preserves the represented root group and torus
equivariance. A simple root's negative is not simple, and distinct simple
roots have distinct negatives; consequently these replacements define one
family with all the required simple-root properties. The chosen family and
its specification are obtained from this existence theorem by choice.

The construction is derived from the actual-root parametrization and
rank-one normalization modules. The combinatorial assembly is the same as
in the reduced-ring `LocalSplitReducedIsomorphismProof`; its inputs here
hold over arbitrary local rings. No reducedness, henselian, noetherian or
characteristic assumption is used. Commutator relations, negative-simple
relations and the full Isomorphism Theorem require further results.
