# Restricting an isogeny to specified maximal tori

`IsIsogeny.torusRestrictionQuasiInverse` constructs a reverse torus
homomorphism and a nonzero integer whose scalar multiplication maps are
the composites in both directions, for the restriction of a general
isogeny to specified split maximal tori. It uses the existing
`TorusRestrictionQuasiInverse` structure and the published integer
quasiinverse theorem for isogenies of split tori.

`IsIsogeny.isIsogeny_torusRestriction` proves that an actual isogeny
between connected reductive groups over any field restricts to an
isogeny between specified maximal tori in a commuting square. The tori
need not split, and the isogeny need not be central or separable.

This is an internal geometric prerequisite for the lattice assertion in
Milne (2017), Proposition 23.5, as stated in
`Langlands.GroupScheme.IsogenyRootDatumStatement`. It is derived from
published Library results rather than introducing another source
convention.

The restriction is finite because its composite with the target closed
torus inclusion equals the composite of a closed immersion and a finite
map. Factor the restriction through its actual schematic image. The
image is a closed torus, reached by an isogeny.

The published finite-surjection centralizer containment theorem then
forces the target torus to factor through that image: both maximal tori
are their full scheme-theoretic centralizers. Cancelling the target
closed immersion shows that the image inclusion has a right inverse.
Its monomorphism property makes this an inverse on both sides. Hence
the image is the entire target torus, and the restriction is finite,
flat and surjective.

The finite-surjection centralizer theorem passes through algebraically
closed fields and descends closed containment. It does not assert that
the full kernel of the ambient isogeny is central. Consequently this
argument retains inseparable maps and possibly nonsmooth kernels.
