# Lifting a smooth group through a monomorphism from the generic fibre

Let `R` be an integrally closed domain with fraction field `K`. Let
`i : H ⟶ L` be a group homomorphism over `Spec R` whose underlying map
is a quasi-compact monomorphism locally of finite type, and let
`e : D ⟶ L` be a homomorphism from a smooth geometrically connected
group. Suppose the composite from the generic fibre of `D` to `L`
admits a scheme lift to `H`. The definition `genericGroupMonoLift`
gives an actual homomorphism `j : D ⟶ H` with `j ≫ i = e`.

The generic lift gives a morphism from the generic fibre to the
pullback `D ×_L H`. Its projection to `D` is dominant by flatness.
Smoothness and geometric connectedness make both the generic fibre
and `D` integral, and the integrally closed base gives normal stalks
on `D`. The schematic image in the pullback therefore maps to an
open of `D`. The unit of the pullback factors through this image
because its generic restriction factors through the generic fibre
of `D` and `Spec R` is reduced. This gives an open containing the
unit and a lift of that open to `H`.

If an open containing the unit in a smooth, geometrically connected
group admits a lift through the monomorphism, multiplication of two
copies of the open gives a smooth surjective cover. The product of the
two lifts on this cover agrees on equal images by monicity, so
effective epimorphism descent gives a scheme morphism from the group
to the source of the monomorphism. Its composite is the original group
homomorphism. Monicity then makes the descended morphism a group
homomorphism.

The construction is an internal consequence of the schematic-image
open and the published product-cover and descent results. The base
may be a valuation domain of arbitrary rank.
