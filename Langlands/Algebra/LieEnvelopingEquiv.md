# Actual complexification and enveloping equivalences

This internal algebra helper transports actual Lie algebra equivalences through
the existing scalar extension and universal enveloping constructions. It uses
Mathlib's `LieAlgebra.ExtendScalars.map` for bracket preservation and the
heterogeneous tensor congruence for the underlying complex linear equivalence.
On a pure tensor the complexification maps `z ⊗ X` to `z ⊗ e X`.

For any commutative base ring, the actual universal enveloping map is the
universal lift of the target generator composed with the supplied Lie
homomorphism. An actual Lie equivalence gives inverse algebra homomorphisms.
Extensionality on the actual enveloping generators proves both inverse laws;
the generator formula identifies the resulting equivalence.

Finally, an actual algebra equivalence restricts to an algebra equivalence of
the actual associative centers. The construction uses Mathlib's injective
subalgebra image equivalence and its equality of the mapped center with the
target center. Its value is exactly the original algebra equivalence applied
to the central element. No geometric tangent comparison or differential action
is supplied by this helper.
