# Finite identity neighborhoods in separated group schemes

`IdentityJet.identityLift` factors the identity section of a group scheme
through its order-`n` identity neighborhood. This is the actual closed
subscheme defined by the `(n + 1)`st power of the identity's ideal sheaf.
The factor is a section of the jet projection.

For a separated structure morphism the identity is a closed immersion,
so the support of the ideal power equals the image of the identity.
The lifted section is therefore surjective on scheme points and the jet
projection is injective on points. Its composite with the lifted section
is the identity, so it is universally closed. If the ambient structure
morphism is locally of finite type, the jet projection is separated and
locally of finite type as well. It is thus proper and locally quasi-finite.
`IdentityJet.finite_projection` deduces its finiteness.

This is an internal extension of the Library's identity jet geometry.
It works over an arbitrary base, including with a non-affine ambient group.
It gives the actual finite jet schemes used
in the conjugation representation approach.
