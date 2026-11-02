# The module structure on the actual affine Lie kernel

Worker 339.

For an affine group scheme `G` over `Spec R` and every commutative `R`-algebra
`A`, this module constructs `Module A (Additive (lieKernel G A))`.
Addition is the existing kernel group law, and scalar multiplication is the
actual map on points induced by the published
`GeneralLinear.DualNumber.epsilonScaleAlg`. The kernel carrier, point carrier,
and scalar operation retain the constructions of `DualNumberKernel`.

The source is Milne, *Algebraic Groups* (2017), source ID
`milne-2017-algebraic-groups`, 10.6, printed p.188 (PDF204), 10.11, printed
p.189 (PDF205), and 10.18–10.20, printed pp.191–192 (PDF207–208).
Milne works over a field with algebraic groups and finitely generated test
algebras. The arbitrary commutative base, unrestricted test algebras, and the
absence of finite type and smoothness assumptions here are derived
generalizations. Affineness is the sole geometric hypothesis used in the
module construction. This file does not construct a Lie bracket.

The implemented proof uses two independent square-zero directions.
`Lie.affineMap_jointly_injective` uses Mathlib's fully faithful `algSpec` and
its affine essential image: algebra maps which jointly distinguish ring
elements distinguish points of any affine target. Consequently the two
projections from `TrivSqZeroExt A (A × A)` to `DualNumber A` distinguish points.
The inclusion of the first direction kills the second projection on a kernel
point, and conversely. The two products of the independent inclusions
therefore have the same projections and are equal. Mapping both directions
to one proves commutativity of the actual kernel group law.

The same projection argument identifies the diagonal inclusion of a tangent
vector with the product of its two independent inclusions. Pushing this
identity along the linear map `(a,b) ↦ f(a) + g(b)` proves
`Lie.squarePointMap_add`. Applying it to multiplication by two scalars proves
addition of scalars. Identity, composition, and zero identities for the actual
square-zero algebra maps prove the remaining module laws. Distribution over
addition follows from the homomorphism on the existing point groups.
The `lieKernelCommGroup` instance copies the original subgroup operations and
adds the proved commutativity law; `lieKernelModule` uses exactly those
operations on the additive type alias.

`lieKernelMap_scale` proves that actual coefficient change commutes with
scaling, using multiplicativity of the coefficient algebra map.
`lieKernelMapLinear G f` bundles the existing kernel map as an `f.toRingHom`
semilinear map. This provides the requested semilinear behavior for all
commutative test algebras, including zero and nonunit scalars. The linear
adjoint representation and the linear matrix comparison are subsequent units.
