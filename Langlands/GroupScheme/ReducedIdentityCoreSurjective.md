# Faithful flatness after restricting to the reduced identity core

`ReducedSubgroup.identityCoreRestriction q` is the actual restricted
homomorphism `(E_red)° → G`, defined by composing the reduced identity-core
inclusion with `q`. Its faithful-flatness theorem is
`ReducedSubgroup.identityCoreRestriction_flat_surjective`; the existing
`identityCore_comp_flat_surjective` also states this directly for the composite.

Over a perfect field, let `E` be an affine group of finite type and `G` a smooth,
connected affine group. The theorem `ReducedSubgroup.identityCore_comp_flat_surjective`
proves that any flat homomorphism `E → G` restricts to a flat surjective homomorphism
`(E_red)° → G`. The reduced identity core and its inclusion are the published
`ReducedSubgroup.identityCore` and `ReducedSubgroup.identityCoreι`.

This is an internal derived consequence of the existing core, image, and flatness APIs.
The core inclusion has open topological range, so flatness and finite presentation of
`E → G` make the restricted range open. The source of the restriction is smooth; its
affine schematic-image projection is therefore surjective. Consequently the topological
range agrees with that of a closed immersion and is also closed. It is nonempty, so
connectedness of `G` makes it all of `G`. Smoothness makes `G` reduced, and topological
dominance is then schematic dominance. The published dominant-homomorphism faithful
flatness theorem supplies the conclusion. No smoothness or connectedness of `E` is
assumed.
