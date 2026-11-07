# Universal enveloping lift into an algebra tensor product

Let `R : Type uR` be a commutative ring, let `L : Type uL` be an
`R`-Lie algebra, and let `A : Type uA` and `B : Type uB` be associative
unital `R`-algebras. All four universes are independent. Both associative
algebras and their tensor product carry their commutator Lie structures.
The Lie structure on `L` remains the supplied one.

For genuine Lie homomorphisms `f : L →ₗ⁅R⁆ A` and
`g : L →ₗ⁅R⁆ B`, `Langlands.Algebra.EnvelopingTensor.sumLieHom`
constructs the Lie homomorphism

`X ↦ f(X) ⊗ 1 + 1 ⊗ g(X)`.

Its additivity and scalar compatibility follow from the tensor
relations. Its bracket compatibility is proved by expanding the
commutator and tensor multiplication: the two cross terms cancel
because the tensor factors commute.

`Langlands.Algebra.EnvelopingTensor.lift` applies Mathlib's universal
enveloping property to this map. It is a unital `R`-algebra
homomorphism from `UniversalEnvelopingAlgebra R L` to `A ⊗[R] B`.
`lift_generator` proves the displayed formula on every canonical
enveloping generator.

This is an internal algebraic construction derived directly from
pinned Mathlib's `Algebra/Lie/UniversalEnveloping.lean` and
`RingTheory/TensorProduct/Basic.lean`. Its purpose is to construct
actual two-place projections of the global archimedean enveloping
algebra from genuine coordinate Lie maps. No external mathematical
assertion is imported. The construction makes no injectivity,
surjectivity, representation decomposition or local-factor claim.
