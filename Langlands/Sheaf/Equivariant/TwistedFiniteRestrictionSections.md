# Discreteness after restriction to an object covered by a finite family

Consider a module sheaf on a twisted site with admissible refinements, and
an arrow between two objects with supplied admissible lifts. Suppose a
finite family in the discrete sieve of a section on the target covers
the source after pullback. `HasFiniteDiscreteCoverAfterRestriction`
records the existence of that family. The section restricted to the
source is then discrete for its supplied lift, when the local action
system consists of lifts.

The discrete-sieve witnesses provide arrows with discrete restrictions
on the target. Local equivariance along those arrows and finite
intersection give a common open subgroup under which the restrictions
are fixed. Restriction equivariance transfers this equality to the
pullback sieve, and sheaf separatedness gives the claimed equality
on the source.

This internal variant of `TwistedFiniteLocalSections` applies when a
finite family becomes covering after shrinking a Galois neighbourhood.
The objects used to test separatedness in the pullback sieve need no
admissible action of their own.
