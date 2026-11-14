# The invariant root-distance function on the apartment quotient

This internal construction works over any field, on the existing quotient of
supplied `KPApartmentData`. The torus is maximal split in a connected reductive
group, and the actual relative roots have a finite type. The explicit
`HasCommonApartments` premise supplies a common translated original apartment
for every pair of quotient points.

`PairApartmentCoordinates` records a rational group element, two original
apartment points and their endpoint equalities. `commonApartmentCoordinates`
chooses this data from the coverage premise. `chosenRootDistance` takes the
canonical root norm of their original affine displacement.

The chart formula uses `GenericApartmentPairNormalizer`: comparing the chosen
coordinates with any other common-apartment coordinates gives one rational
element carrying both apartment images to the alternative pair. The published
two-point comparison gives one actual normalizer with the same two values.
Its affine linear part preserves the canonical root norm. The chosen distance
therefore equals that norm on every translated apartment, independently of
the choice used in the definition.

Common apartments then prove invariance under the existing rational-point
action. The equivalent formula is the square root of the finite sum of
squared actual root evaluations; its normalization is exactly the existing
`RootTranslationMetric` normalization. The function is nonnegative, symmetric,
zero on the diagonal, and zero only at equal points. Apartment injectivity
used for definiteness is the published arbitrary-field algebraic theorem.

The last two lemmas show uniqueness from the translated chart formula, or from
rational-point invariance and the original-apartment formula. They express
uniqueness of a function on the supplied quotient, without choosing a new
quotient or group action.

The provenance is the existing quotient, the explicit common-apartment
premise, the two-point normalizer construction, the published canonical root
norm and apartment injection. The triangle inequality, retractions,
completeness, nonpositive curvature and coefficient action are not outputs
of this unit. In particular it constructs a distance function with the stated
properties; a metric still requires the further building-theoretic argument.
