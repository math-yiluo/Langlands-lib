# Derivations and augmented dual-number algebra maps

This internal construction works over arbitrary commutative rings `K` and `A`,
with a `K`-algebra structure on `A` and a specified augmentation
`r : A →ₐ[K] K`. The `A`-module structure on the coefficient ring `K` is
explicitly induced by `r.toRingHom.toAlgebra`: the action is `a • c = r a * c`.
The base `K`-module structure remains its usual multiplication action.

The forward map sends a derivation `D` to `a ↦ (r a, D a)` in the actual
dual-number algebra. The Leibniz rule proves multiplicativity, and vanishing
on base scalars proves compatibility with the `K`-algebra structure. Conversely,
the second coefficient of an augmented algebra map is `K`-linear; its
multiplicativity and prescribed first coefficient prove the Leibniz rule.
The two constructions are inverse by coordinate extensionality, giving
`derivationDualNumberEquiv`.

Addition of derivations adds their second coefficients. Multiplication by any
base scalar `c` corresponds to composition with the published algebra map
`epsilonScale c`, which sends epsilon to `c` times epsilon. The zero
derivation is the constant lift of `r`.

The construction follows directly from Mathlib's definitions of derivation
and the dual-number multiplication, and reuses the published epsilon-scaling
map. It does not identify sheaf-defined tangent spaces or cohomology and does
not classify line bundles.
