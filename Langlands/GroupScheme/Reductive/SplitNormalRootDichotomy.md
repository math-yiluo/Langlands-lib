# The actual normal-root dichotomy for split maximal tori over arbitrary fields

Derived extension of the published algebraically closed
normal-root dichotomy to arbitrary fields when the specified maximal torus is
split. It retains actual all-test root groups and full centralizers, imposes
no characteristic restriction, and applies at every universe parameter.

`splitNormalRootDichotomy` states that each actual root subgroup of this
specified split maximal torus is contained in a supplied smooth connected
closed normal subgroup or centralizes the whole subgroup on every test and
refinement.

The proof chooses an actual root datum for the split pair, then realizes the
specified root by an index of that datum. Extend the field to its algebraic
closure. Semisimplicity, splitness, maximality, smoothness, connectedness, and
normality pass to this extension through their published comparison theorems.
The transported root datum shows that the base-changed character remains an
actual root. Apply the published algebraically closed normal-root dichotomy.

Actual root subgroups commute with base change. For the containment
alternative, fpqc reflection of containment in a represented closed subgroup
returns containment in the original subgroup. For the centralizing
alternative, use the actual closed normal full-centralizer representative
`closedNormalCentralizer`. Full centralizers commute with base change, so the
same fpqc containment reflection applies to this representative. Its exact
range equality returns the original centralizer statement.

`splitNormalRootPlacement` turns this all-test alternative into actual maps
from any supplied root-group representative into the normal subgroup or any
supplied representative of its full centralizer. Both alternatives retain
the original ambient composite. The maps are obtained by lifting inclusions
of represented subgroup functors; this construction is the arbitrary-field
split analogue of the existing `normalRootPlacementOfRootLines`.

This module constructs no Cartan-component factor or root-datum matching of
such a factor. Its provenance is internal derived interface material, and it
uses no downstream local rank-one classification or Kneser–Tits input.
