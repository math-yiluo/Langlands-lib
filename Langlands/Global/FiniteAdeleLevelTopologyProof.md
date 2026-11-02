# Proof of the topology of actual finite-adelic level rings

Author: Worker 208.

`finiteAdeleLevelTopology` proves exactly
`FiniteAdeleLevelTopologyStatement` in arbitrary common universe `u`.

The local-factor projection is continuous by coordinate evaluation in the
restricted product, restriction to the level subspace and corestriction to
each completed integer ring. The inverse assembly map first takes values
in the principal-filter restricted product imposing integrality outside
`S`. That principal-filter product has the coordinate-induced topology.
Each coordinate of assembly is one projection from one of the two factors,
so this intermediate map is continuous. Mathlib's continuous inclusion
from this principal-filter restricted product into the actual cofinite
restricted product proves continuity into the ambient finite adele ring.
Corestriction then proves continuity into its level subring. These two
continuity results and the existing inverse identities establish the
homeomorphism for the original ring equivalence.

The open-embedding assertion for transitions follows by composing with
the open inclusion of the larger level into the ambient finite adele ring:
the composite is exactly the open inclusion of the smaller level.

For exhaustion, an actual finite adele has a finite set of nonintegral
coordinates by its restricted-product membership condition. That finite
set gives a level containing it. Finally, the level containing any given
adele is open. Continuity of a map on every level therefore implies
continuity at that adele. This proves the final-topology characterization;
the reverse implication is restriction of a continuous map.

These arguments concern the actual existing subspace and product
topologies and the original maps. They do not change topologies by
transport. Their derived source role and retained global-field and
scheme-point limitations are stated in the statement's paired Markdown.
