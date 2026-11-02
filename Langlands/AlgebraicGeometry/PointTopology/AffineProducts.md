# Actual affine product-point comparisons

Author: Worker 105.

Source: Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), Proposition 2.1 and its proof, printed page 2.
Registered source `conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

This construction unit uses the published actual point carrier and intrinsic
evaluation topology. For commutative `R`-algebras `A`, `B`, and `S`,
`AlgPoint.tensorPointPair` restricts an algebra map from `A ⊗[R] B` along
Mathlib's two tensor-factor inclusions. The inverse `tensorPointLift` uses
Mathlib's `Algebra.TensorProduct.productMap`; it sends `a ⊗ b` to `p(a)q(b)`.
`tensorPointEquiv` proves that these are inverse. These are actual algebra
maps, with no topology, finite generation, separation or presentation
hypotheses. Continuity of the forward restriction map needs only a topology
on `S`, since each component is published continuous precomposition.

In a common universe, `SpecProductPoint R A B S` consists of actual morphisms
from `Spec S` to the actual scheme pullback of `Spec A` and `Spec B` over
`Spec R`, satisfying the displayed base equation. The construction
`specProductTensorEquiv` composes with Mathlib's `pullbackSpecIso` and checks
that equation in both directions. Its direction is from pullback points to
spectrum-of-tensor points; its inverse composes with the inverse scheme
isomorphism. `specProductPointPairEquiv` then combines this with the published
actual affine scheme/algebra point equivalences and `tensorPointEquiv`.

The topology on actual scheme product points is transported from the affine
evaluation topology on the tensor coordinate algebra.
`specProductTensorHomeomorph` records this transport. The inverse bijection's
continuity and the resulting product topology comparison over a topological
value ring are separate statement and proof obligations. In particular this
unit does not assert topological product compatibility, general fibre-product
compatibility, axiomatic uniqueness, or completion of Proposition 2.1.

The tensor construction and short algebraic inverse checks implement the
standard affine-coordinate product used in Conrad's proof; the explicit
scheme pullback bridge is a derived host comparison with Mathlib's existing
affine pullback theorem, rather than a new scheme construction.
