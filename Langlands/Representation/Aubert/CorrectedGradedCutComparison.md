# Actual cut maps on corrected graded support quotients

This internal construction lifts the actual representative comparison to
every vector of the actual corrected Jacquet support quotient.

`correctedSupportOrbitClass_cutMap` computes the genuine quotient cut map
on a supported class. It is the class of the actual normalized cut map of
the supported induction vector. The cut map preserves the corrected
support, and its Jacquet descent takes radical classes to radical classes
of the actual cut map.

`coherentGradedOrbitIntegralIso` specializes the actual graded support
isomorphism to the single coherent family of actual orbital measures.
Its target retains the actual integrated Haar-ratio coefficient, the
positive source half modulus on the normalized source Jacquet module,
and the target inverse half-modulus twist.

`coherentGradedOrbitIntegralValue` evaluates the actual coherent graded
isomorphism, and its class formula computes that evaluation on every
supported class.

`coherentGradedOrbitIntegralValue_cutMap` compares the actual quotient
cut map with the actual orbit coefficient map at every target Levi element
for every quotient vector. Its hypotheses are the cut inclusion, source
increase at both ends, upward closure of the upper and lower support sets,
and membership of the permutation in the corrected two-sided Weyl support.
The target membership follows from monotonicity under adding source cuts.
There is no additional premise about a choice of representative or measures.

The proof lifts an arbitrary quotient vector to a supported induction
vector by the proved surjectivity of `correctedSupportOrbitClass`, computes
its actual quotient cut map, and applies the evaluation formulas for the
two graded isomorphisms. The coherent representative comparison then gives
the desired coefficient equality.

All primes, supplied p-adic topologies, arbitrary ranks including zero, and
independent field and coefficient universes are retained. This is the
individual graded-map comparison; it does not assemble an entire graded
complex or assert homology vanishing or signed effectivity.
