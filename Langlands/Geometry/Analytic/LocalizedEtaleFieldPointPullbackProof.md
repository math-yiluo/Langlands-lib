# Full field-point preservation of localized etale pullbacks

`localizedEtaleFieldPointPullback` proves exactly the existing proposition
`LocalizedEtaleFieldPointPullbackStatement.{u,v,uL} K L`. The base field
`K : Type u` is complete and ultrametric. The extension field `L : Type uL`
is complete, algebraically closed and ultrametric, with the given
`NormedAlgebra K L` structure. The space and chart index universe `v` is
independent of both field universes.

The result applies to every supplied genuine pullback square in the actual
localized category whose first cospan leg is etale. Its image under the actual
`localizedFieldPointFunctor L` is a pullback in types. Thus every compatible
pair of full field points has exactly one full field-point lift, including
all chart evaluations and restriction compatibility. No Hausdorff,
compactness, equal-universe, nontrivial-valuation, or supplied preservation
hypothesis is added.

The proof applies the internal assembly theorem
`localizedEtaleFieldPointPullbackStatement_of_algebra` to the proved canonical
domain completed-residue comparison `domainCompletedResidueSurjectivity`
and the proved unrestricted actual affinoid finite Banach base-change theorem
`AffinoidPushout.finiteBanachPushout`. Neither remains an additional premise.
The imported domain comparison concerns the actual canonical map on completed
residue fields for full affinoid-domain representations, and the base-change
theorem concerns the original right map into the actual affinoid pushout.

The assembly first uses strong localization descent to replace arbitrary
localized cospans and projections by strong numerators, transporting the
supplied pullback along denominator isomorphisms. Forward full recognition
comparisons replace a strong etale cospan by one with literal finite original
chart pairs. The supplied square transports along these comparison
isomorphisms. Finite Banach base change keeps each needed actual pushout
spectrum small in the original space universe. Compatible bounded chart
evaluations extend to a full point on that pushout, and the supplied localized
pullback universal property supplies the desired full lift.

For uniqueness, every candidate point has a faithful local kernel-quotient
representative admissible to both fixed image charts. Its complete nested
images make the two quotient pullbacks compatible. The actual pushout maps
to this quotient, whose injective character identifies its full point with
the fixed pushout point. Faithful common-chart detection proves equality of
both strong triangles. Localized pullback uniqueness then identifies the
representative map with the fixed lift; applying the actual full functor
proves equality of all field-point data. Functorial transport through the
recognition and localization isomorphisms gives the original square.

This proof is an internal combination of the named Library constructions.
