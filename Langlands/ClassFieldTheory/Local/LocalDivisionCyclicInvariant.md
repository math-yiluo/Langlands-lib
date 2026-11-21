# Local Brauer invariant of a cyclic division parameter

Take a finite arithmetic-unramified Galois stage of reduced degree and an embedding into the central division algebra. Suppose a division unit conjugates that field by its arithmetic Frobenius. Its reduced-degree power is the image of a base-field unit, the central cyclic parameter.

The chart `divisionOppositeArithmeticChart` uses the basis of implementing-unit powers for the left field action and the right action of the opposite algebra. Its relative class is the positive carry class of the central parameter. The Library's finite unramified invariant evaluates this class as the normalized order of that parameter divided by the reduced degree in the rationals modulo the integers. Passing from the opposite algebra to the original one negates the result.

This fixes the convention for the power and arithmetic conjugation relations in Drinfeld, *Coverings of p-adic Symmetric Regions* (1976), §2 A–B, printed pp. 109–110. In particular the power with order one gives positive reciprocal invariant for the opposite class in the Library's convention.
