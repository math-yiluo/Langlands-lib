# Regular actions from flat square-zero kernels

Let `R` be a commutative base ring, `I` a square-zero ideal, `G` an arbitrary smooth group scheme over `Spec R`, and `H` a flat affine group scheme over that base. The square-zero condition is supplied as `Fact (SmoothLifting.SqZero I)`. The coefficient module is the actual base reduction kernel `M = Additive(kernel G I)`. No affineness or separatedness hypothesis is imposed on `G`.

The construction takes an actual scheme morphism `s : H.X → G.X`, together with, for every affine `R`-algebra `A`, a homomorphism `s₀(A) : H(A) → G(A/IA)` and an equality saying that `s(h)` reduces to `s₀(A)(h)`. These are explicit inputs. The module does not construct the morphism `s`, the reducing homomorphisms, or their comparison with a prescribed scheme-theoretic reduction.

`coordinateAlgebra_flat` proves that the chosen affine coordinate algebra of a flat affine source is flat over `R`. It transports scheme-theoretic flatness through the chosen coordinate isomorphism and uses the characterization of flat spectrum maps.

For a flat test algebra `A`, `flatConjugationAction` transfers the genuine linear conjugation action on `Additive(kernel G (IA))` through the canonical flat comparison with `A ⊗[R] M` of `Lie.NonaffineKernelFlat`. `flatComparison_naturality` and its inverse form restate the comparison's naturality in the regular coefficient functor. `flatConjugationAction_naturality` combines these comparisons with naturality of actual conjugation. No kernel comparison on nonflat tests is used.

`liftTensorAction` applies the genuine kernel action of the map `s`, whose reduction is the supplied homomorphism, at each flat test algebra. It is natural between flat tests because `s` is an actual scheme morphism. `liftKernelCoaction` evaluates that action at the universal source point over the flat coordinate algebra, on vectors `1 ⊗ m`. This is an `R`-linear map `M → C_H ⊗[R] M`.

`liftKernelCoaction_action` proves that specializing this coaction at a point over any flat test algebra recovers the original tensor-valued kernel action. The proof uses naturality along the universal point's coordinate specialization, then test-algebra linearity and tensor induction. This identity supplies both requirements of `UniversalModuleAction`: the identity is checked over `R`, and multiplication at the independent generic pair is checked over `C_H ⊗[R] C_H`, which is flat.

`regularKernelRepresentation` is the resulting `ModuleRepresentation M H` on all affine test algebras. Its naturality and group-action laws follow from the universal construction in `AffineModuleActions`. The theorem `regularKernelRepresentation_action` identifies it with genuine kernel conjugation on every flat test. On a nonflat test it is the regular action obtained by coordinate specialization; the module asserts no comparison with that test's actual reduction kernel.

This is an internal derived construction for the homomorphism deformation argument. The new action uses the actual nonaffine kernel and its canonical flat scalar extension, with the supporting modules `Lie.NonaffineKernelCocycles` and `Lie.NonaffineKernelFlat` unchanged. It introduces no cohomological vanishing, defect primitive, or homomorphism lifting existence theorem.
