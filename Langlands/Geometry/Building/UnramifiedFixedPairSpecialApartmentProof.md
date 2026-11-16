# A common centralizing special apartment for two fixed points

The theorem `Langlands.Geometry.Building.unramifiedFixedPairSpecialApartment`
proves the published proposition
`Langlands.Geometry.Building.UnramifiedFixedPairSpecialApartmentStatement`
in arbitrary universe `u`, for either characteristic. Its assumptions and
conclusion are exactly those of that proposition.

The proof first applies
`Langlands.BruhatTits.IntegralModels.recoveredFixedBuildingPairModels`
to the two coefficient-fixed points. This constructs compatible full and
neutral integral models over the original integers and over the actual
maximal-unramified integers. The construction forms two separate point models,
intersects their integral-point subgroups, and descends the resulting smooth
model. It therefore applies before a common apartment for the two points has
been chosen. The equality
`RecoveredBuildingFixerModels.baseChange_full_integralPoints` identifies the
coefficient extension of the lower full model with the ambient character
valuation kernel intersected with the pointwise fixer of the pair.

The proof then invokes
`Langlands.Geometry.Building.unitFixedPairApartmentOfNeutralModel`
on the lower relative component model and this equality. Maximal splitting of
the original source supplies its split-subtorus hypothesis. Unit fixation of
the two points supplies the two endpoint hypotheses.

The supporting construction uses `unitFixedNeutralTorusData` to extend the
source to a closed split integral torus in the neutral model and
`unitFixedContainingTorusData` to enlarge it to a relative torus with maximal
residue inclusion. Its actual maximal-unramified pullback is split.
`IntegralModel.isMaximalSplitTorus_residue_baseChange` transports maximality
to that pullback's actual residue inclusion, using the coefficient comparison
and splitting. The specified generic isomorphism and its commuting equation
are retained throughout.

`centralizingPairApartmentOfNeutralTorus` then applies
`RelativeComponentModelData.neutralPairReference` to obtain a closed reference
torus in a common translated chart and
`RelativeComponentModelData.neutral_baseChange_integralPoints_le_fixingSubgroup`
to prove that integral points of the same ambient neutral model fix both
endpoints. It invokes
`KPApartmentData.centralizingConjOfResidueMaximalIntegralTorus` with these
data. Integral torus conjugacy preserves coverage because its conjugating
point fixes the pair. Centralizer conjugacy and coefficient transport then
give a point centralizing the original source, normalizer-valued coefficient
differences, and coordinates for both endpoints in the same translated
apartment.

Finally the theorem takes the rational point and its specifications from this
construction. The proof uses the original field's local-field structure and the
actual coefficient extension; it adds no local-field hypothesis on the maximal
unramified field. This is an internal assembly of the named constructions for
the Library formulation of corrected Kaletha–Prasad Proposition 9.3.11(1).
