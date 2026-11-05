# Second countability of actual arithmetic-level model points

The theorem `adelicLevelModelSecondCountability` proves the conjunction
`AdelicLevelModelSecondCountabilityStatement` in an arbitrary common universe.
It retains finite-type nonaffine models over the actual outside-S integer
rings, the original scalar actions, empty S, function fields with finite
constants, and all number-field infinite factors. It adds no separation
assumption.

The local helper first base changes a finite-type model to an actual local
factor. Local finite type and quasi-compactness are preserved by this base
change. `schemePointSecondCountability` then proves second countability of
the local-model point space in its existing affine-chart final topology.

For curve places, `curvePlace_countable` supplies the countable index and
`curvePlaceCompletion_secondCountableTopology` supplies second countability
of each completed field. The completed integer ring inherits it as a
subspace. `adelicLocalFactorUnits` supplies the local open-unit condition;
the actual factors already have their local topological-ring instances.
For number fields the proof uses `finitePlace_countable`,
`finiteCompletion_secondCountableTopology` and
`infiniteCompletion_secondCountableTopology`. It treats every infinite
place as well as the two sorts of finite factors. The infinite-place set
is finite, and the completed integer rings inherit second countability
from their completed fields.

In each characteristic the dependent product of the local point spaces is
second countable. The arithmetic-level topology was defined by inducing
this product topology along the actual local-model point map.
`IsInducing.secondCountableTopology` therefore proves the conclusion
directly. This last step uses no injectivity or surjectivity theorem.

The argument implements the countable-base property accompanying Conrad's
Section 3 level construction and prepares Section 4's full adelic result.
Source: Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), registered as
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`,
Propositions 2.1 and 3.1 on printed pp.2 and 4 and the level product and
countable-base discussion on printed pp.8–9. The local second-countability
prerequisite is derived from the finite-coordinate and finite-cover
constructions, as its own target explains. Full adelic final-topology
second countability requires a further countable-cover argument.
