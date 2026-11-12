# Analytic charts from split submersive presentations

For a submersive presentation of the actual coordinate algebra whose variables
are `Fin d ⊕ σ` and whose dependent-variable map is `Sum.inr`, the evaluated
dependent Jacobian is the transpose of the presentation Jacobian matrix.
Its determinant is the actual algebra-point value of the presentation's
Jacobian unit, so it is nonzero at every solution.

The actual affine scheme point homeomorphism and `presentationPointHomeomorph`
identify actual relative points with this solution space.
`RegularChart.ofSubmersivePresentation` transports the analytic polynomial
fibre chart through that homeomorphism. Its forward coordinates are evaluations
of the free generators with denominator one. Every actual algebra element has
a polynomial representative, and evaluation along the inverse chart equals
evaluation of that representative; the polynomial inverse-evaluation theorem
gives exactly the required `ContDiffOn k ω` field. The accompanying source
membership lemma follows from the polynomial chart's source lemma.

Worker 115 adapts Workers 362 and 1650's published
`PointManifold.General.SubmersivePresentationCharts`. It uses analytic
coefficient-field calculus directly and does not restrict scalars to the reals.

Throughout this module, `k : Type u` is an arbitrary complete nontrivially
normed field, the scheme is affine over `Spec k`, and its actual point carrier
is `PointTopology.RingPoint k X k` with its published evaluation topology.
The analytic order is `ω` over `k`. There is no characteristic, archimedean,
positive-dimension or point-nonemptiness assumption.
