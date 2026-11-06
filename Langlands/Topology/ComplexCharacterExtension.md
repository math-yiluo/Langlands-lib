# Extension of complex characters from open subgroups

This is an internal helper for the weight-one CM character construction. It
establishes general extension results for abelian groups and their topological
counterparts, using Mathlib's algebraic closedness of the complex numbers and
Baer's criterion. There is no number-field or class-field input in this module.

`complexUnitsDivisibleByNat` takes a nonzero complex root of a complex unit.
Its additive version is divisible by every positive natural number and hence
by every nonzero integer. Baer's criterion then extends a homomorphism to the
complex units along any injective homomorphism of abelian groups. The proof
uses additive type tags so that Mathlib's integer-module extension theorem
applies, and transports the resulting homomorphism back to multiplicative
notation. The domain and ambient group may have arbitrary universes.

A homomorphism continuous on an open subgroup is continuous at the identity,
and therefore everywhere. Thus an algebraic extension of a continuous complex
character from an open subgroup is automatically continuous. Finally an open
homomorphism has an open image and is a quotient map onto that image. A
continuous character trivial on its kernel descends to this open image and
then extends continuously to the whole target group. No finite-index premise
is required.

These general facts supply only the extension step. Applying them to an idele
quotient still requires proving the concrete kernel compatibility and openness.
