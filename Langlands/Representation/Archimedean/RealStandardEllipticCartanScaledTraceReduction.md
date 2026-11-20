# Elliptic Cartan comparison with a separate constant for each block list

`RealStandardEllipticCartanScaledTraceLimitsStatement` uses the actual compact test traces
at the separated regular Cartan points. Its support formula gives zero below the Cartan's
elliptic rank. At the Cartan's rank the formula is the finite numerator times a common
Cartan factor and a nonzero constant for the original block list. The list constant is fixed
across the Cartan coordinates and the enumeration. The Haar measure and nontrivial test
filter at each point are common to the lists.

The Lean proof enumerates the two original lists, preserving membership and rank. An
intertwiner gives equality of the actual traces on each continuous test. If either list
had more induced blocks, its trace would have a nonzero limit at a separated regular
point on its own Cartan and the other trace would converge to zero there. Uniqueness of the
limit excludes this. The equal total ranks then give equal character counts.

After fixing these counts, the trace limit identities and cancellation of the common
nonzero Cartan factor give proportionality of the numerators on the separated regular
coordinates. Continuity extends that proportionality to all coordinates. The numerator
scalar rigidity theorem then gives equality of the full numerators. This proves the exact
comparison from the stated trace limits, keeping the ranks, positivity, irreducibility,
and actual intertwiner of the original target.

The reduction is internal and keeps the two trace limit formulas as inputs.
