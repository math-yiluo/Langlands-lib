# Signed finite boundaries and equivariant cochain models

This internal construction uses supplied whole-group lifts and the actual
finite discrete free-sheaf sums from `TwistedFreeRepresentableFinite`, with
all of that module's assumptions. `SignedBoundary L M` gives a finite family
of integer coefficients, index maps between the finite families, and ordinary
arrows intertwining the supplied whole-group actions. Both positive and
negative coefficients, and an empty list of arrows, are allowed.

`ordinaryMap` is the sum of the induced ordinary free-sheaf maps multiplied
by these coefficients. `discreteMap` forms the same sum in the discrete sheaf
category, using explicit eventual-equivariance proofs for both families.
`discreteMap_restriction` proves the ordinary restriction square for this sum by
additivity, compatibility with integer multiplication, and the individual
finite-sum map squares. `discreteMap_restriction_hom` gives the same square using the
forward comparison isomorphisms.

`discreteFreeSheafSumLift_restricts_cochain` applies the fixed-family lift to
a specified ordinary cochain. Each supplied fixed section must be the section
represented by the corresponding component of that cochain. Coproduct
extensionality and the ordinary representing equivalences then identify the
restriction of the lift with precisely the specified cochain.

The provenance is internal: all constructions are finite sums, the published
representing equivalences and the restriction identities. No geometric
existence, differential compatibility or exactness follows from finite
presentation alone. Those remain separate inputs.

`ordinaryFreeSheafSum` abbreviates the actual ordinary finite coproduct.
`FiniteFreeThreeTermModel J R S Q n` supplies three finite families of global
lifts, their eventual-equivariance proofs, upper and lower signed boundaries,
ordinary isomorphisms to degrees `n+2`, `n+1`, `n` of `Q`, and the two ordinary
differential squares. These squares are hypotheses, beyond termwise finite
presentation.

`equivariantModel` forms the actual discrete finite sums and their signed maps.
The ordinary restriction isomorphisms followed by the supplied chain-term
isomorphisms give the three comparisons. The signed restriction squares and
the two ordinary differential squares prove both equivariant differential
squares. The resulting generic `EquivariantThreeTermModel` reflects the zero
composite; if `Q` is exact at `n+1`, it also reflects exactness because this
restriction functor preserves finite limits and finite colimits.

`cochainLift` additionally takes a discrete coefficient `I`, an isomorphism from
its ordinary restriction to `F`, a cochain `x : Q.X (n+1) ⟶ F`, and fixed middle
sections representing the components of the cochain transported to `I`.
The finite fixed-family lift and its restriction identity supply the precise
middle-cochain equation, and the generic assembly gives the existing
`EquivariantCochainLift`. For injective `I`, the existing primitive descent
therefore applies. No injectivity assumption is needed to construct this model.

This assembly proves equivariant exactness from supplied ordinary exactness;
it does not establish the existence of the families, their eventual
equivariance, their ordinary differential squares, or the required fixed
sections. In particular, it leaves general quasi-etale lifting compatibility
and geometric finite Cech-model construction open, and does not prove the
analytic comparison.
