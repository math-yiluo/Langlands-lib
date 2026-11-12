# Simple connectedness of actual degree-two norm-one groups

Authors: Worker 124.

`Langlands.GroupScheme.CentralSimpleUnits.DegreeTwoNormOneSimplyConnectedStatement`
is the following proposition. For every field `K` and every finite-dimensional
central simple `K`-algebra `A` with `Module.finrank K A = 4`, the actual
`CentralSimpleUnits.normOne K A` is algebraically simply connected. Its
meaning is the published `IsSimplyConnected`: the group is semisimple and
every incoming central isogeny from a semisimple group is an isomorphism.
The field, algebra and schemes lie in an arbitrary common universe, and
there is no characteristic restriction or supplied splitting hypothesis.

This is a focused internal structural statement needed by the concrete
hyperbolic quaternionic cover construction. It includes both the
quaternion division algebra and the split algebra `M₂(K)`. Its expected
proof route is to construct the actual norm-one base-change comparison
with binary special-linear matrices over a splitting field, establish
the split group's simple connectedness from the integral coroot
criterion, and descend by the published field-extension reflection
result. These comparisons and proofs are obligations, not extra
premises in the proposition.

The statement is introduced as an internal consequence target of the
published root-datum, reduced-norm and simple-connectedness framework;
no external source transcription or proof is claimed by this unit.
It does not assert the hyperbolic product morphism is a spin cover, the
comparison with any larger supplied spin cover, or Kneser–Tits generation.
