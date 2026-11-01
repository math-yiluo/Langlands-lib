# Actual graded support quotients and orbit coefficients

This internal construction connects the actual corrected Jacquet support
quotient to the compact orbit coefficient. It uses the supplied actual
orbital measures and retains the target inverse half-modulus twist.

`correctedSupportOrbitClass` sends a supported normalized-induction vector
to its actual target-radical class in the corrected upper Jacquet image and
then to the quotient by the corrected lower image. Every element of the
quotient has such a representative: quotient projection is surjective and
the upper image is the actual image of the induction support space.

`correctedJacquetOrbitIso_hom_class` computes the existing actual
Jacquet orbit isomorphism on these classes. The support-image quotient
comparison first sends the class to the radical class of its support
quotient projection. Mapping the actual orbit restriction through normalized
coinvariants then gives the radical class of `correctedOrbitRestriction`.

`correctedGradedOrbitIntegralIso` composes that actual isomorphism with the
supplied-measure compact orbit integral equivalence. The latter is twisted
by the target inverse positive half modulus, exactly as in normalized
Jacquet. Its output retains the actual integrated Haar-ratio coefficient
and the positive source half modulus on the normalized source Jacquet
module. The evaluation theorem computes its value on every supported
class by the previously defined actual orbit-equivalence value.

The support and lower support have their stated upward closure properties,
and the permutation belongs to the corrected two-sided Weyl support.
No classification, irreducibility, finiteness or homology claim is used.
Arbitrary primes, supplied topologies, ranks including zero, and independent
field and coefficient universes are retained.
