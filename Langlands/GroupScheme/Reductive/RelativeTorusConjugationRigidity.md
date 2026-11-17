# Torus conjugation from local algebra generator comparisons

This internal derived construction compares two actual homomorphisms over a
commutative ring. A torus point may be parametrized by an arbitrary relative
scheme, which need not be affine.

`torusConjugateAlgebraHom` pulls back the second homomorphism to a commutative
algebra and conjugates it by the evaluated torus point. Its evaluation formula
holds on every test scheme over that algebra.

`TorusConjugates.of_localAlgebraHom` assumes an affine target. If the first
homomorphism agrees with that conjugate over every commutative local algebra and
every algebra point of the parameter scheme, the torus point conjugates the
second homomorphism into the first on every relative scheme test. The proof
tests each desired equality on spectra of local rings, supplies the algebra
structure induced by the structural map to the original base, and applies the
imported local-ring-point extensionality theorem. Local algebras with nilpotents
are included.

`TorusConjugates.of_localWeylGenerators` assumes a reductive source, a supplied
split fibrewise maximal torus, and a supplied full fibrewise root datum on the
coordinate lattices. A base of that datum and a family of root maps are supplied;
the simple-root maps must be actual root parametrizations, and the Weyl points
built from each simple root and its opposite must act by the corresponding
reflection. The source structure map is assumed affine, and the target scheme
is affine.

For every commutative local algebra and each algebra point of the parameter
scheme, the hypothesis is `AgreeOnWeylGenerators` between the pulled-back first
homomorphism and `torusConjugateAlgebraHom`: equality on the pulled-back
coordinate torus, equality on the simple-root maps, and equality of the images
of each negative-simple root point with parameter minus one. The conclusion is
`TorusConjugates` on the entire group, with the same torus point.

The proof obtains simple reflection words from finiteness and reducedness of
the supplied full fibrewise root datum. It transports source reductivity,
maximality, the full root datum, root parametrizations and Weyl normalization
to each local algebra by the imported base-change theorems. The published
`hom_ext_of_weylGenerators` then gives equality of the actual group-scheme
homomorphisms over that algebra. The local-algebra criterion above gives
conjugation on all tests. No locality of the original ring or affineness of the
parameter scheme is required.

The construction and proof are derived from actual base-change point
equivalences, the point formula for inner automorphisms, and
`CellGluing.hom_ext_of_localRingPoints` in
`LocalSplitLocalAlgebraCellIsomorphism`, together with the imported full-source
generator theorem in `SplitHomomorphismRigidity` and the source transport
theorems in `FibrewiseRootDatumBaseChange` and `LocalSplitRootBaseChange`.
They assert no structural existence of root data or conjugating torus points,
and do not supply the local generator-agreement hypotheses for finite maps.
These remain separate inputs to the host isogeny rigidity argument.
