# Group transport for cuspidality comparisons

Author: Worker 158.

These internal constructions supply the representation transport needed for
the actual one-block Levi comparison. They derive directly from published
coinvariant, fixed-vector, smoothness, and admissibility definitions. They
use arbitrary commutative coefficient rings, independent group and carrier
universes, and no finite-dimensionality hypothesis on the carrier.

`Jacquet.coinvariantsMapEquiv` identifies coinvariants of the pullback of rho
along a group homomorphism f, at a subgroup N, with the coinvariants of rho
at the image subgroup f(N). Both maps send the class of v to the class of v.
The quotient universal property applies because the two collections of
relations have the same images. Each image-subgroup element has a preimage
in N. Quotient-map surjectivity proves that the two maps are inverse.
Neither injectivity nor surjectivity of f is required.

`fixedVectors_comp_mulEquiv` identifies the actual fixed submodules under a
group equivalence e. The image of K is written as the preimage of K under
the inverse equivalence. The equality follows by evaluating the two inverse
identities. This form makes openness immediate when e is a continuous group
equivalence.

`isAdmissible_comp_continuousMulEquiv` uses continuous pullback for smoothness
and that fixed-submodule equality for finite generation at every open
subgroup. `isAdmissible_comp_continuousMulEquiv_iff` applies the same argument
to the inverse equivalence. No topological-group axiom or compactness is
needed: the Library definition of admissibility tests all open subgroups.

These results do not assert the single-block geometry or the cuspidality
comparison itself. Their future application uses the actual Levi embedding,
its constructed topological inverse, and proved subgroup image identities.
