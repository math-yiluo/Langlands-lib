# Actual dual-number identity kernels

Worker 339.

This module constructs `Langlands.GroupScheme.lieKernel G A` as the actual
subgroup kernel of reduction from `G(DualNumber A)` to `G(A)`. The point carrier
is a morphism from the published `algSpec R` test scheme to `G.X`, and its group
law is the published `GroupScheme.points` law.

The source is Milne, *Algebraic Groups* (2017), source ID
`milne-2017-algebraic-groups`, 10.6, printed p.188 (PDF204), 10.11, printed p.189
(PDF205), and 10.18–10.20, printed pp.191–192 (PDF207–208). Milne works over a
field with algebraic groups and considers finitely generated test algebras.
The arbitrary commutative base ring, arbitrary group scheme, and unrestricted
commutative test algebras here are derived generalizations for these elementary
kernel constructions. No affine or finite type hypothesis is needed for them.

`Lie.affineMap` uses the actual contravariant spectrum map. `Lie.reduction`
uses `TrivSqZeroExt.fstHom`, and `Lie.constant` uses
`TrivSqZeroExt.inlAlgHom`; reduction after the constant inclusion is proved to
be the identity. `lieKernelMap` uses the published
`GeneralLinear.DualNumber.coefficientAlgMap`. `lieKernelScale` uses the
published `GeneralLinear.DualNumber.epsilonScaleAlg`, including zero and
nonunit scalars. Kernel membership follows from commutation with reduction.

`lieKernelConjugation` restricts conjugation by the constant lift of an actual
point. Its naturality in the test algebra and its commutation with epsilon
scaling are proved from functoriality, the group homomorphism laws on points,
and the corresponding identities of actual dual-number algebra maps.

`lieKernel_generalLinear` proves by reflexivity that the generic kernel at
`GeneralLinear.groupScheme n R` is exactly the published
`GeneralLinear.DualNumber.PointKernel n R A`, retaining the existing carrier
and coordinates.

This unit supplies the group kernel and its actual maps. Commutativity, the
module laws, linear adjoint representation, and weight spaces are subsequent
constructions and are not asserted here.
