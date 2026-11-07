# Induction along a map and coinduction

Author: Worker 1646.

This is an internal comparison construction used in the proof of inductivity
of local Euler factors. It compares two existing Library constructions; no
additional representation, induction convention or mathematical hypothesis is
introduced.

Let `K` be a field, `H` and `G` groups in independent universes, `ι : H →* G`
an injective homomorphism, and `A` a finite-dimensional representation of `H`.
The published `induceAlong ι hι A` first restricts `A` to `ι.range` along
`InductionAlong.rangeInverse ι hι`, then induces from that subgroup. Its vectors
are equivariant functions `f : G → A`. Mathlib's `Representation.coindV ι
A.representation` describes functions on exactly the same domain and codomain.

`rangeCoinductionEquiv` is the linear equivalence between these function
spaces that leaves every function value unchanged. Its construction does not
require the image to have finite index. To carry subgroup equivariance to
`H`-equivariance, it inserts the range element represented by `ι h` and uses
`rangeInverse_apply`. Conversely, it applies `H`-equivariance to the inverse
image of an arbitrary range element and uses `apply_rangeInverse`.

`rangeCoinductionEquiv_apply` records the unchanged function values, and
`rangeCoinductionEquiv_action` records compatibility with the ambient `G`
action: both actions send `f` to the function `x ↦ f (x * g)`.

Now suppose `ι.range` has finite index and `I` is a normal subgroup of `G`.
`invariantCoinductionEquiv` is a linear equivalence from the actual Library
object `invariants I (induceAlong ι hι A)` to the `I`-fixed subspace of
Mathlib's coinduction along `ι`. It restricts the previous equivalence and its
inverse. A fixed-vector equality is carried over by evaluating it at each
`x : G`. `invariantCoinductionEquiv_action` states compatibility with every
element of `G` on these invariant subspaces. The theorem follows directly
because both maps preserve the underlying functions.

The coefficient, group and representation-carrier universes remain independent;
there is no continuity assumption. The source constructions are imported by
Lean name from `Langlands.WeilDeligne.InductionAlong`,
`Langlands.Weil.Representation.Invariants` and their Mathlib dependencies.
The provenance is internal: all assertions are direct comparisons of these
already published function-space definitions. No claim of the full Euler-factor
induction identity is made by this module.
