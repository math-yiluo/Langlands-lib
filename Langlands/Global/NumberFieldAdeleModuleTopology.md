# Finite-free coordinates on full number-field adeles

For number fields `K` and `L` in an arbitrary common universe, an algebra
`K → L`, and any finite indexed field basis `b` of `L` over `K`,
`Langlands.Global.adeleBasisHomeomorph` is a homeomorphism

`Adeles L ≃ₜ (ι → Adeles K)`.

Both sides carry their original Library topologies. Every infinite place and
the full restricted product of finite places are retained. No compactness or
reduction-theory hypothesis is used.

This is an internal derived construction. Its published inputs are
`numberFieldAdeleTensorEquiv`, the canonical full adelic tensor algebra
equivalence, `adeleTrace` with its continuity and principal compatibility,
and the original continuous `adeleInclusion`. The remaining algebraic inputs
are Mathlib's tensor-product basis coordinates and the trace-dual basis for
a finite separable field extension. Number-field extensions satisfy those
finiteness and separability hypotheses.

The implemented proof first establishes linearity of the full trace over
the full adelic inclusion. On infinite components this is completion-trace
linearity summed over places above a fixed place. On finite components it is
the published finite-adele trace-linearity theorem.

`adeleBasisEquiv` composes the inverse canonical tensor equivalence with
coordinates in `b`. Tensor induction and the trace-dual identities prove the
exact formula

`adeleBasisEquiv K L b y i = adeleTrace (algebraMap L (Adeles L) (b.traceDual i) * y)`.

Thus every coordinate is continuous for the original topology on `Adeles L`.
The inverse is the finite sum

`∑ i, algebraMap L (Adeles L) (b i) * adeleInclusion (x i)`.

Continuity of the original inclusion, multiplication and finite addition
proves continuity of this inverse. These two continuity results package the
algebraic coordinate equivalence as `adeleBasisHomeomorph`.

This unit supplies coordinates for the subsequent Weil-restriction topology
comparison. It does not identify character norm-one subgroups or prove
compactness of a rational quotient.
