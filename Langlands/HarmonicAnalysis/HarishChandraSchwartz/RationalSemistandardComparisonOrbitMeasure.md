# Orbit points and measure for the actual normalized comparison

Waldspurger (2003), VI.3, compares the values of the source section at
`ω` and of the target section at `sω`. The two sections in the Library
use their own chosen base inducing objects in the actual twist orbits.

`orbitPointComparison` applies the literal inverse Levi pullback and
recenters at the target base. It uses the same compact Weyl lift as
`WeylSectionComparisonData.smoothComparison`. On each actual inducing
object `orbitPointComparison_representative` identifies its class with
the class of the object used in the target coefficient fiber. Every
point of the source orbit is represented in these fibers.

`orbitPointComparison_measurePreserving` applies the source-normalized
orbit measure comparison at these exact base points. The integral
change of variables retains both the character restriction-kernel scale
and the reciprocal self-twist factor. The displayed finite-index
hypotheses are inherited from the two source orbit measures.
