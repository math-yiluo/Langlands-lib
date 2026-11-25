# Exact pushout pullbacks on faithful local representatives

This internal construction works over a complete ultrametric normed
field `K` with a normed extension field `L`. The algebra, space and
extension-field universes are independent. All presentations are
saturated, with space and chart-index universes equal to the space
universe. No completeness or ultrametric condition on `L` is
required by this module.

Consider a commuting square of complete strong morphisms, with
maps `r : P → A`, `s : P → B`, `f : A → C` and `g : B → C`
such that `r ≫ f = s ≫ g`. Choose a chart `k` containing the full
field point `p` on `P`, charts `i` and `j` receiving the images of
`k` under `r` and `s`, and a chart `t` receiving the complete images
of `i` and `j` under `f` and `g`.

The two bounded chart pullbacks from `t` to `k` agree exactly.
Indeed, the full strong composition formula computes each
composite pullback, and equality of the strong composites
identifies them. Composing with the quotient map for the actual
kernel of `p`'s evaluation at `k` gives
`chartTestPullback_square`: the direct representative-chart
pullbacks agree over the actual chart algebra at `t`.

Apply the universal property of the actual affinoid pushout of
the two chart pullbacks from `t`. Its target is the actual
faithful quotient algebra at `k`, a complete ultrametric normed
commutative `K`-algebra. This produces `chartTestPushoutPullback`,
a bounded map from that pushout algebra into the faithful quotient.
Composing with either original pushout leg recovers exactly the
corresponding direct representative-chart pullback. The
pushout's bounded-hom extensionality proves uniqueness from these
two exact equations.

This provides a concrete affine algebra input for comparing a
faithful local representative with a fixed finite pushout test.
The module requires no smallness hypothesis for the pushout spectrum:
it constructs the bounded algebra map only. It makes no assertion
that the pushout spectrum fits the space universe or that a given
analytic square is a categorical pullback. No domain
completed-residue comparison is used in these algebra identities.

The provenance is internal, from the complete strong composition
formula, the actual local character-kernel quotient and the
constructed affinoid pushout's bounded universal property. This
module does not prove final localized full-field-point preservation.
