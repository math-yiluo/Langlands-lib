# Internal direct sums and support after scalar extension

Worker 416. This internal linear algebra lemma compares two internal direct sum
decompositions over fields `k` and `K`. A scalar-extension linear equivalence
from `K ⊗[k] V` to `W` is assumed to send every pure vector from the component
`A i` into `B (f i)`, where the index map `f` is injective.

`internalComponentProjection` constructs a coordinate projection from the
inverse of the internal-sum linear equivalence, followed by evaluation at
the chosen index. It is used in the preservation proof below.

`component_eq_bot_iff_of_tensorEquiv` proves that `B (f i)` is zero if and only
if `A i` is zero. Reflection uses faithful flatness of the field extension:
`1 ⊗ x` vanishes only when `x` vanishes. For preservation, project the second
internal direct sum onto `B (f i)`. If `A i` vanishes, this projection vanishes
on extended vectors from every old component, using injectivity of the index
map and uniqueness of the second decomposition. The old components span `V`,
so it vanishes on every `1 ⊗ x`. Tensor induction then makes the projection
zero on all of `W`. Its restriction to `B (f i)` is the identity, forcing
that component to be zero.

No surjectivity of the index map, finite-dimensionality or restriction on the
field extension is assumed. The provenance is the implemented argument from
Mathlib's internal direct sum and faithfully flat tensor interfaces.
