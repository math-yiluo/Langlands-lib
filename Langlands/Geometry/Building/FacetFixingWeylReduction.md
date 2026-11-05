# Chamber transport and affine Weyl images from facet fixing

This internal geometric construction uses the published affine-root arrangement,
chamber and affine Weyl group definitions. It applies over arbitrary independent
universes for the vector space, affine torsor and acting group, and includes rank
zero. No assertion about an actual reductive group's facet stabilizers is proved
here.

`IsLocallyFiniteReflectionArrangement.exists_regularPoint` chooses a vector on
which every derivative root is nonzero, using finite avoidance of the kernels of
those nonzero linear forms. Starting at any affine point, a sufficiently small
positive displacement along this vector preserves all initially nonzero root
signs by the published local-sign lemma. Each root initially equal to zero becomes
nonzero by the choice of the vector. This gives a regular point even when the root
set is empty. `regularPoint` and `baseChamber` choose that point and its actual
sign-equivalence chamber.

`chamberWeylTransport` assigns to a root-preserving affine automorphism the unique
affine Weyl element carrying a supplied chamber to its image. Its image and
uniqueness lemmas follow from the published `affineChamberSimpleTransitivity`
theorem. The resulting map is not asserted to preserve multiplication.

`range_eq_affineWeylGroup_of_chamber_fixing` assumes a homomorphism into the affine
automorphisms, that its range preserves the roots and contains the affine Weyl
group, and that the stabilizer of one chamber fixes that chamber pointwise. For
an element of the acting group, take its chamber transport and lift that Weyl
element using the lower inclusion. The lift's inverse times the original element
stabilizes the chamber, hence fixes it pointwise. The published affine-span lemma
makes this correcting affine automorphism the identity, proving that the original
element's image is the chosen Weyl element. The opposite containment is the given
lower inclusion.

`range_eq_affineWeylGroup_of_facet_fixing` chooses `baseChamber` and applies this
argument, using that a chamber is a facet. Its assumptions retain both image
containments and the pointwise facet-fixing obligation. This is an intermediate
reduction toward the simply connected normalizer theorem, not its proof. No AS 5,
Tits-system or group-scheme comparison constructor is supplied by this module.

The provenance is internal: finite linear-algebraic avoidance from Mathlib,
published local-sign geometry, affine chamber simple transitivity, and affine
span rigidity are composed to construct the transport map and prove the stated
conditional image equalities. There is no claim that this module formalizes an
additional theorem from external literature.
