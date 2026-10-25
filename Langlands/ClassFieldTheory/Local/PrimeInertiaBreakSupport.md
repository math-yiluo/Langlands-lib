# Prime inertia filtration and inverse-Herbrand support

This module supplies the elementary part of the prime break argument.
It uses the actual lower groups and the actual constructed inverse Herbrand
function for an arbitrary supplied topological realization. Its directly
proved helper theorems support `PrimeRamificationBreakProof`.

The Galois group has prime cardinality, so each subgroup is either trivial or
the whole group. The first trivial lower group exists by the published
termination theorem, and its index is positive because the zeroth group is
inertia and inertia is assumed to be the whole group. One less than that index
is the break. Minimality and antitonicity yield the two branches, including the
case of break zero. The first group is the whole group precisely when the
break is positive.

For the inverse formula, the actual lower-group orders equal the extension
degree through the break and one afterwards. The published floor formula for
`herbrandPhi` at a natural input becomes a finite sum. Before the break this
sum has only terms equal to the degree. Beyond the break it is split into a
prefix of those terms and a tail of ones. Evaluation at the natural candidate
`t + degree * (n - t)` gives `n`. The published inverse identity then gives the
required formula for `herbrandPsi`, with the equality branch at `n = t` intact.

This is a derived conditional implication; it does not derive total inertia
from canonical ramification indices or identify a positive break with the
residue characteristic. Those arithmetic obligations are proved in
`PrimeRamificationArithmeticSupport`. The source conventions are Serre,
*Local Fields* (1979), Chapter IV §§1 and 3 and Chapter V §3; the parent proof
Markdown records the registered source and applicable errata.

Author: Worker 96.
