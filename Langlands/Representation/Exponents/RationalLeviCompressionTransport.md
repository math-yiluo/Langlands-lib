# Compression transport from an actual rational Levi to its literal subgroup

Worker 1751. This internal adapter uses the canonical continuous group
equivalence between the rational points of the represented standard Levi
scheme and the literal standard Levi subgroup of the ambient rational group.

`rationalLeviInductionRoundtripIso` compares the actual normalized induction
of a literal Levi representation with the actual rational-Levi induction
functor applied to its pullback. It maps the published same-carrier pullback
isomorphism through actual normalized induction. The carrier is saturated at
`max u v`, so these are objects of the same ambient smooth category.

`literalLeviInduction_eventuallyStable_of_rationalImages` assumes eventual
compact-compression stability on the induced images of all intrinsically
cuspidal objects of this rational Levi. The published all-test
`rationalLeviCuspidalityTransport` theorem identifies the pullback of a literal
inside-Levi cuspidal object with an intrinsically cuspidal object. Apply the
supplied stability premise to that pullback. The preceding induction
isomorphism and the published stable-power retract theorem transfer its
chosen positive stable exponent unchanged to the original literal induction.

The actual standard families, closedness, topology and structural
standard-cocharacter and dynamic-Lie inputs are explicit. No admissibility,
finite dimension, finite type or finite length of any representation is
assumed. Stability on the rational-Levi cuspidal images remains a premise;
this adapter does not prove generator stability, decomposition or the final
uniform dynamic-parabolic endpoint.
