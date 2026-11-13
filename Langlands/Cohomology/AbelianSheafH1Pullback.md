# Arbitrary-map compatibility of the Čech-to-H¹ comparison

This internal prerequisite concerns actual abelian sheaves on topological spaces.
Let `f : X ⟶ Y` be any continuous map between universe-`u` spaces, let `A` be an
abelian sheaf on `Y`, let `B` be one on `X`, and let `k : A ⟶ f_* B`.
No exactness assumption on direct image is imposed.

The module uses the Ext-defined `pushforwardMap f k n` from
`AbelianSheafCohomologyPullback`. Its degree-zero normalization is
`pushforwardMap_equiv₀`: under the canonical cohomology/global-section
identifications, the map is exactly `k.hom.app (op ⊤)`. The proof reduces Ext⁰
to morphisms and uses the specified constant-sheaf adjunctions and uniqueness
of left adjoints. `pushforwardMap_factor` expresses factorization through
`H.map k`, and `pushforwardMap_equiv₀_symm` gives normalization in the reverse
identification direction.

The selected construction `adjointComplexMap` takes a morphism of short
complexes `φ : S ⟶ T.map f_*` to a morphism `S.map f⁻¹ ⟶ T` by adjoining its
three components. The commutative squares follow from the same adjunction.
Consequently `pushforwardMap_δ` says, for short exact `S` and `T` and `n+1=m`,
that applying `pushforwardMap f φ.τ₁ m` after the connecting map for `S`
equals applying the connecting map for `T` after `pushforwardMap f φ.τ₃ n`.
This follows from exactness of inverse image and the previously constructed
Ext connecting-map compatibility.

For an ordered family of opens `U` on `Y`, `transportRepresentative` maps a
Čech primitive and its quotient section along `φ`, then transports cochains
to the inverse-image family. `transportRepresentative_value` identifies its
connecting class with the cohomological pullback, using the preceding
connecting-map and degree-zero results.

The main compatibility result is `comparisonHom_pullback`. For every finite
family `U` covering `Y` and every class `x` in its fixed-family Čech H¹,
comparison of the class obtained by applying `k` and transporting to the
inverse-image family equals `pushforwardMap f k 1` of the original comparison.
Here the comparison is the actual `AbelianSheafCechH1.comparisonHom`, and the
cochain transport is the published `CechPullback.h1Equiv`.

The proof extends `k` to a map from the chosen injective sequence of `A` into
the direct image of the chosen injective sequence of `B`. Direct image
preserves injectives because its left adjoint, inverse image, preserves
monomorphisms. The map on cokernels is constructed by the cokernel universal
property; exactness of the direct-image sequence is not needed. On a Čech
cocycle choose a representative, transport it, and use the comparison's
value formula and `transportRepresentative_value`.

Provenance is internal: these are compatibility constructions and consequences
of Mathlib's actual inverse-image adjunction, Ext cohomology, and the Library's
Čech representative comparison. This module supplies a prerequisite for
square-zero Picard obstruction naturality; it does not assert the target
Picard or relative module-cohomology comparison.
