# Compact sections of injective smooth sheaves are invariants-acyclic

Author: Worker 141.

This internal helper proves that the compact-section functor sends injective
smooth equivariant sheaves to representations with vanishing positive derived
invariants, for the unchanged compact-group assumptions of the host task.

First, compact sections of the actual degree-zero smooth Godement functor are
identified with a smooth cofree representation. The implemented isomorphism
composes the published coinduced Godement model, the comparison between compact
sections of the smooth coreflector and smooth compact sections, the actual
indexed-family coordinates, and the compact-family/cofree isomorphism. The
previous cofree acyclicity theorem then gives vanishing of positive derived
invariants on these compact sections.

The Godement coaugmentation of an injective smooth sheaf is monic, so injectivity
supplies a retraction. Applying compact sections followed by any positive
derived invariants functor preserves this retraction. Its intermediate object
is zero by the preceding argument; hence the identity of the resulting object
is zero. This proves the claimed vanishing, without asserting that compact
sections preserve injectivity.

All coefficient rings and space assumptions are those of the host target; no
averaging or coefficient invertibility is used. The derived Hom comparison and
its naturality remain separate obligations.
