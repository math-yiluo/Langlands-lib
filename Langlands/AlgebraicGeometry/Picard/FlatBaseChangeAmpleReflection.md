# Ampleness reflection under flat surjective affine base change

For a Cartesian square of schemes over a flat surjective morphism between
affine schemes, `LineBundle.isAmple_of_affine_flat_surjective_baseChange`
proves that a specified line bundle is ample if its actual pullback is ample.
The schemes and rings are arbitrary in one scheme universe. There is no
noetherian, finite-type, separatedness, or field hypothesis.

This internal generalization follows the existing field-base-change proof.
The affine surjection reflects compactness and quasi-separatedness of the
underlying scheme from the ample pullback. The construction
`FlatAmpleReflection.sectionsIsoOfAmplePullback` then gives the canonical
scalar sections isomorphism for every line bundle using the published
quasi-compact quasi-separated flat base-change theorem.

At any downstairs point choose an affine neighbourhood. Upstairs ampleness
gives a section of a positive tensor power whose generation open is contained
in its inverse image. A further positive power vanishes after restriction
to the base change of the closed complement, even if this base change is
nonreduced. Canonical flat base change for sections applies both to the scheme
and to that closed complement. The support-preserving coefficient lemma then
extracts a downstairs positive-power section vanishing on the complement and
generating at the original point. Its whole generation open is contained in
the chosen affine neighbourhood and is affine by the published affine
generation-locus argument. These sections establish the ampleness definition.

The last theorem transports an arbitrary affine-base square through the
canonical isomorphisms with spectra of global rings. Flatness of the induced
ring map follows from flatness of the original affine morphism. The theorem
concerns a supplied square and a supplied actual line bundle; it constructs
neither a scheme descent datum nor its effective quotient.

The provenance is internal: the implementation generalizes
`FieldBaseChangeAmpleReflectionProof` using the flat-ring coefficient lemma
and the already general QCQS scalar sections base-change theorem.
