# Topology of actual finite-adelic level rings

Author: Worker 208.

`FiniteAdeleLevelTopologyStatement` quantifies a Dedekind domain `R`, its
fraction field `K` and all finite sets of height-one primes, in an arbitrary
common universe `u`. It has four conclusions about the existing actual
`finiteAdeleLevel` subrings.

- `finiteAdeleLevelProductEquiv` is a homeomorphism. The domain uses the
  subspace topology from the actual finite adele ring, and the target uses
  the product of the actual completion and completed-integer topologies.
- Every transition inclusion for `S ⊆ T` is an open embedding.
- Every actual finite adele belongs to some finite level.
- A map from the finite adele ring to any topological space in universe `u`
  is continuous exactly when its restriction to every finite level is
  continuous. This characterizes the final topology through the levels.

This is derived finite-sector infrastructure for Brian Conrad, *Weil and
Grothendieck approaches to adelic points* (December 31, 2011), printed p.1,
the description of the adelic ring as a direct limit of open level rings,
and printed pp.6–8, Theorem 3.6 and its local product factors. Registered
source `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The existing finite-level construction and Mathlib restricted-product
topology give the actual objects to which the assertion applies.

This statement concerns only the finite sector of a Dedekind model. It
does not identify all places of a global function field, supply
archimedean factors, assert a categorical ring colimit universal property,
or construct topologies or comparison maps on nonaffine scheme points.
The source's nonempty all-place convention on `S` remains a separate
global-field obligation.
