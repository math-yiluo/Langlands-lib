# Conjugation action on actual identity jets

For a separated group scheme `G` over `S` and every natural number `n`,
`IdentityJet.conjugationAction G n` gives an action of `G` on its order-`n`
identity jet scheme over `S`. The jet is the closed subscheme cut out by
the `(n + 1)`-st power of the identity ideal.

On a test scheme `U` over `S`, the cartesian comparison of identity jets
identifies a `U`-point of the original jet with a section of the jet of
the base-changed group. The jet functor applies to the inner automorphism
defined by the base-changed group point. Transporting the resulting jet
section back to a `U`-point gives `IdentityJet.conjugatePoint`. Composing
this point with the closed inclusion into `G` gives `g * x * g⁻¹`, where
`x` denotes the image of the original jet point in `G(U)`.

Restriction along any map of test schemes commutes with this formula in
the group, so the monomorphism of the jet into `G` gives naturality of
`conjugatePoint`. Evaluating on the two projections from the product of
`G` and its jet defines the action morphism. The same monomorphism reduces
the identity and multiplication laws on every test scheme to the group
laws for conjugation. The resulting scheme action evaluates to
`conjugatePoint` on every pair of test points.

This is an internal construction from the Library's functorial identity
jets, their cartesian base-change comparison, inner automorphisms, and the
construction of scheme actions from laws on test points.
