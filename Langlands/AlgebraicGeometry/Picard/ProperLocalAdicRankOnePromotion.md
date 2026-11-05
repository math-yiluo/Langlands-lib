# Promoting adic stalk frames to an actual line bundle

This internal construction is the rank-one promotion step after coherent
algebraization. It produces an actual line bundle while preserving the given
module sheaf as its underlying module.

For a locally finitely presented module sheaf `M` and a point `x` with
noetherian local ring, `Modules.stalkRankOneEquivOfAdicQuotients` constructs a
frame of the actual stalk from frames of all quotients by positive powers of a
proper ideal in that local ring. It applies the proved local algebra
construction `Langlands.Algebra.AdicRankOne.equivOfAdicQuotients`; finite
presentation of the actual stalk is supplied by `Modules.finitePresentation_stalk`.

For a universally closed morphism `f : X → Spec R` with `R` local,
`isLocallyFreeRankOne_of_closedFibre_stalkEquivs` proves that frames of the
actual stalks on the closed fibre make `M` locally free of rank one everywhere.
Finite presentation spreads each stalk frame to an open trivialization.
The resulting rank-one open contains the closed fibre. The existing theorem
`open_eq_top_of_contains_closedFibre` then makes that open all of `X`.

Finally, on a locally noetherian `X`,
`lineBundleOfClosedFibreAdicStalkQuotients` combines these two arguments.
Its hypothesis supplies a proper ideal separately at each closed-fibre point,
together with frames of every positive-power quotient of the actual module
stalk. The ideal is fixed across all powers at each point. The construction
returns the original module equipped with the proved local rank-one property.
It assumes universal closedness, so it applies in particular to proper
morphisms. It assumes neither base flatness nor projectivity.

These are derived internal constructions, using the Library's implemented
stalk finiteness, rank-one spreading and proper-local open-cover results.
This unit does not construct coherent algebraization and does not identify
ordinary-pullback stalks on actual adic scheme thickenings with the local
quotient modules in its hypothesis. That geometric identification remains a
separate obligation in proper formal line-bundle effectivity.
