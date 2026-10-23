# Natural first isomorphism for subfunctor quotients

This internal algebraic construction uses the published `RepSubfunctor`
quotient functor. Given subfunctors `S,T` of a representation-valued functor
`F`, the denominator is exactly `S.lowerInUpper T`: the inverse image of
`S` under inclusion of `T`. No containment assumption on `S,T` is needed.
The coefficient commutative ring, acting monoid, representation carrier, and
source category retain their independent universes.

`quotientNatLift` descends a natural transformation from `T.toFunctor` to
any functor `H` into the same representation category, provided each component
vanishes on that denominator. It is constructed with `Submodule.liftQ`.
Equivariance and naturality are checked on representatives, using surjectivity
of the actual quotient projection. Its projection law is definitional.
`quotientNatLift_unique` proves uniqueness from the natural factorization law.

`quotientNatIsoOfSurjective` constructs a natural isomorphism from the actual
quotient functor to `H` when the supplied transformation is surjective at each
object and its kernel is exactly the denominator. The kernel formula for
`Submodule.liftQ` proves injectivity; surjectivity follows by projecting a
preimage of the original component. `Representation.IntertwiningMap.ofBijective`
and `NatIso.ofComponents` then construct the isomorphism. Forward and inverse
formulas identify the class of a vector with its image under the original map.

The provenance is the elementary universal property and first isomorphism
theorem for modules, applied to the existing equivariant quotient definitions.
This helper assumes the stated kernel and surjectivity facts; it proves no
geometric restriction, compactness, or extension assertion. Those must be
established separately before applying it to the Mackey support filtration.

Author: Worker 112.
