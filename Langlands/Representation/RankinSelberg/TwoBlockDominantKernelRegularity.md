# Regularity of the actual dominant rectangle kernel

This is an internal regularity lemma family for the lower kernel in JPSS
(1983), Section 4.10(2), printed page 419, registered source
`jpss-1983-rankin-selberg`. Its mathematical inputs are the published actual
five-block matrix, supplied rectangle Haar measure and invariant quotient
kernel. The measurability assertions are derived infrastructure rather than
additional assertions attributed to the source.

The two rectangles may have zero dimensions. Block functionals may be zero.
The test is an actual coefficient-image function of any smooth
representation; neither irreducibility nor a topology on the representation
or tensor carrier is imposed. Field, test and block carrier universes remain
independent.

The proof first checks continuity of the unipotent matrix and its inverse
entry by entry in the five-block coordinates. Continuity of the rank
inclusion and group multiplication gives joint continuity of the source's
actual matrix in the group and rectangle coordinates. Smooth section
evaluation and smooth coefficient evaluation are locally constant scalar
functions. Multiplying these continuous evaluations by the continuous
determinant weight gives continuity of the weighted raw kernel for every
complex parameter. `continuousKernel` bundles this same actual kernel
with its joint continuity proof; its evaluation theorem is definitional.

The total complex rectangle integral and the total integral of the raw
norm are measurable by strong measurability of parameter integrals. This
uses sigma-finiteness of the exact supplied rectangle measure and does not
require fiber integrability. The set of integrable fibers is measurable
by the measurable parameter-integrability theorem. Finally, all three
results descend to the actual lower quotient using its closed subgroup
and the measurable quotient criterion. There is no choice of coset
representative or change in Haar normalization.

No convergence bound, outer integrability, or almost-everywhere fiber
integrability is asserted. In particular, the real raw-norm profile remains
the integral of the raw norm, not the norm of the complex average.
