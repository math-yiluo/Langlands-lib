# Exact local normalization for actual unramified root restriction

For every nonarchimedean local field in the existing Library sense, this
internal construction specializes actual root-valuation and apartment field
restriction to `Langlands.LocalGalois.Separable.inertiaFixedField F`. It uses
the already constructed normalized integer valuation
`MaximalUnramified.valuation F`. No local-field instance is asserted for
that actual inertia fixed field.

`realOrderCharacter` casts the source-positive integer unit order of that
valuation to additive real values, bundled as a homomorphism to
`Multiplicative ℝ`. Its evaluation is definitionally
`IntegerValuation.order (valuation F)`. The proved exact integer normalization
on original field elements implies `realOrderCharacter_base`: restriction
along the actual field-unit extension map is precisely the existing
`localFieldOrder F`, with no scaling factor or changed sign.

`realOrderCharacter_nontrivial_on_base` uses the existing original
`SplitTorusValuation.uniformizerUnit F`. Its original normalized order is
one, and exact order restriction makes its extended unit-character value
one as well. Thus nontriviality on original units is established for this
application, rather than retained as a premise.

`restrictRootValuation` applies full field-valuation restriction to an
upstairs valuation on the literal base changes of the original split torus
and group. It assumes the original group smooth and affine, the inclusion
monomorphic and split, original opposite factor pairs, and upstairs
split-torus compatibility with the constructed integer valuation order.
Neither V3 nor unit nontriviality is a separate input. The returned family is
definitionally the literal actual field restriction, and
`restrictRootValuation_compatible` proves its compatibility with exactly
`localFieldOrder F`.

`restrictApartment` applies the constructed field-restricted apartment to a
supplied upstairs apartment compatible with that integer order, then uses
the proved scalar-order identity to give the existing downstairs
`KPApartmentData i (localFieldOrder F)`. Its carrier is definitionally the
literal image of the supplied upstairs carrier; the carrier identity is
recorded by `restrictApartment_carrier`. The orbit and normalizer stability
come from actual apartment field descent, so the existing normalizer action
is retained.

The provenance is the existing normalized maximal-unramified valuation and
its exact base-order formula, the original uniformizer order theorem, and
the preceding internal full valuation/apartment restriction. No new
external theorem is introduced. Arbitrary universe and the Library's equal-
and mixed-characteristic local fields are retained. Original opposite pairs
and the upstairs valuation or apartment for the original split torus base
change remain supplied. These constructions do not supply initial upstairs
data or restriction from a larger torus, affine-root/facet/quotient descent,
the five geometric axioms, or the supplied-model building comparison.
