# The Bernstein centre as a product of component rings

For a standard family, `bernsteinComponentDatum` chooses a standard
cuspidal datum in every inertial class. `BernsteinComponentProduct` is the
dependent product of their rings of invariant regular functions.
`componentProductOn` transports the corresponding coordinate to the
component ring of any datum in that class. Its evaluation law identifies
the values at associated twists.

`BernsteinCenterComponentProductStatement` derives a ring isomorphism
from the centre of the smooth representation category to this product
from `BernsteinCenterFunctionsStatement`. At an arbitrary datum and
unramified character, evaluation of the transported coordinate gives the
scalar by which the central element acts on the normalized induction of
the twist.

For a central element, the proof restricts its scalar family to the chosen
data. The scalar descriptions agree on associated parameters, so
`componentProductOn` recovers the scalar on every twisted induction.
Those inductions are nonzero. Uniqueness of the scalar shows that
evaluation preserves the ring operations. The detection clause of
`BernsteinCenterFunctionsStatement` gives injectivity by comparing the
action on every twisted induction.

For surjectivity, transport each coordinate to all data of its class by
the change-of-datum equivalence. Two associated parameters have a common
associated parameter of the chosen datum, so the transported functions
give equal values at them. Extend each function by zero to the character
domain of `BernsteinCenterFunctionsStatement`. Its existence clause
supplies a central element with those scalars. Restricting the scalars
back to the chosen data recovers the original tuple.

The product expresses the second sentence of David Renard,
*Représentations des groupes réductifs p-adiques*, French edition of
9 July 2026, VI.10.4, Theorem, with the evaluation convention of Remark 1
(printed pp. 211–212, PDF pp. 217–218). The change of datum uses the
component description in VI.7.1 (printed pp. 180–181, PDF pp. 186–187).
The source is registered as
`renard-2026-representations-groupes-reductifs-padiques` with SHA-256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
