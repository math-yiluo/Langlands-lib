# Square-zero reduction kernels of affine group schemes

Let `G` be an actual affine group scheme over `Spec R`, let `A` be any commutative `R`-algebra, and let `I` be an ideal of `A`. `SquareZero.reduction` is the actual coefficient-point homomorphism `G(A) → G(A/I)`, and `SquareZero.kernel` is its group-theoretic kernel.

Using the Library's chosen affine coordinate presentation, `kernelCoordinates` identifies actual kernel points with algebra maps from the coordinate algebra to `A` that lift the identity augmentation modulo `I`. The coordinate algebra acts on `A`, and hence on `I`, through the actual identity augmentation.

When `I² = 0`, `kernelDerivationEquiv` identifies the underlying set of kernel points with derivations from the coordinate algebra into the actual ideal `I`. It composes `kernelCoordinates` with Mathlib's `derivationToSquareZeroEquivLift`. The derivation associated to a point is its coordinate algebra map minus the identity augmentation. `kernelDerivationEquiv_naturality` verifies the coefficient formula for compatible kernel points under any algebra homomorphism.

`idealCotangentHomEquiv` applies the universal property of relative differentials at the identity with values in `I`. Its composition with the preceding equivalence gives `kernelCotangentEquiv`, a bijection with linear maps from the actual identity cotangent module into `I`.

For a smooth affine group, the identity cotangent module is finite projective. The canonical dual-tensor-Hom equivalence and the Library's actual Lie-kernel/cotangent-dual comparison then give `kernelTensorEquiv`:

`ker(G(A) → G(A/I)) ≃ I ⊗[R] Additive(lieKernel G R)`.

This declaration asserts a bijection of underlying sets. The module does not prove that these bijections identify multiplication in the reduction kernel with addition in the derivation or tensor module, nor that the tensor bijection is compatible with conjugation. Those comparisons remain necessary for the cohomological deformation bridge.

No flatness hypothesis on `A` or `I` is used. The coefficient on the right is the actual ideal of the test algebra. If a test ideal arises by extending an ideal of the base, this module does not replace it by a tensor product from the base without the required hypotheses. It also makes no assertion for a nonaffine target group.

This is an internal derived construction from the Library's actual affine-point coordinates, identity cotangent and smooth affine Lie module, together with Mathlib's square-zero ideal/derivation equivalence and finite-projective dual-tensor-Hom equivalence. It introduces no additional literature assertion and supplies no homomorphism lifting result.
