# Integral character and cocharacter automorphisms

For a commutative group scheme `T` over an arbitrary field `k`, the existing
`RealTorusSpace.cocharacterAut σ` sends a cocharacter `ν` to `ν ≫ σ.hom`.
Its inverse postcomposes with `σ.inv`, and `cocharacterAut_apply` records this
formula. The existing character automorphism sends `χ` to `σ.inv ≫ χ`.
`RealTorusSpace.latticePairing_aut` states that these two automorphisms preserve
the integral character–cocharacter pairing, by associativity and cancellation
of the inverse morphisms.

These declarations are moved unchanged from
[RealTorusAction](../../Geometry/Building/RealTorusAction.md) into the shared
torus layer. Their names, field hypotheses, formulas and proofs are preserved.
Both the building's scalar-extension construction and
[StandardLeviRootTransport](../Rational/StandardLeviRootTransport.md) reuse them.
This is an internal algebraic construction and makes no new root-transport or
standard-Levi conjugation assertion.
