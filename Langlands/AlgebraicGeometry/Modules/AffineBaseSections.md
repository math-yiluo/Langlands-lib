# The structure map from an affine base to sections

For a commutative ring `R`, a scheme `X`, a morphism `f : X → Spec R`, and an
open `U` of `X`, `AdicStalkQuotient.baseSectionHom f U : R →+* Γ(X, U)`
is the canonical map from the base ring to sections. It composes the inverse
of the global-sections equivalence for `Spec R` with `f.appLE ⊤ U le_top`.
No additional algebra structure on sections is chosen.

The definition is moved unchanged from `Modules/AdicStalkQuotient`, keeping
its original full name. This permits the same construction to serve
`Picard/AffineBaseChangeKernel` without importing the adic development.
