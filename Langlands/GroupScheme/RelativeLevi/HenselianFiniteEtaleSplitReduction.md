# Split data after a finite étale refinement

This derived helper constructs full split data from a factored torus
neighbourhood and reduces `HenselianFiniteResidueQuasiSplitStatement` to two
published proposition interfaces. It imports published root-space,
coordinate-pullback, affine torus-neighbourhood and Borel-lifting results.

`localSplitDataOfFactoredNeighbourhood` assumes a reductive group over the
spectrum of an arbitrary commutative ring, a closed fibrewise maximal coordinate
split torus over an affine neighbourhood, and an actual factorization of the
canonical map from the spectrum of a local algebra through that neighbourhood.
It returns the actual coordinate torus map in a subtype certified by
closedness, fibrewise maximality, existence of a full fibrewise root datum,
and freeness of its actual root exponent spaces of rank one.
It pulls back the same torus in the same finite coordinates. The actual
pullback-composition isomorphism and the supplied factorization equation put the
ambient group in the direct base change used in the target statement.
Closedness and maximality are preserved by this isomorphism. The local
root-space assembly then supplies the full fibrewise root datum and actual
rank-one root-space isomorphisms. The factorization lemma needs no étaleness,
finiteness or henselian hypotheses.

`henselianFiniteResidueQuasiSplit_of_inputs` proves the exact target
conditionally on `RelativeBorelSchemeStatement` and
`Langlands.CommutativeAlgebra.HenselianFiniteEtaleRefinementStatement`,
in the same universe. It applies the published
`henselianFiniteResidueQuasiSplit_of_borelScheme` to obtain a relative Borel
over the original henselian base with finite residue field. The published
`exists_etale_affine_split_maximalTorus` supplies an affine étale neighbourhood
of the closed point with a closed fibrewise maximal coordinate split torus.
The refinement premise supplies a local finite étale algebra and its actual
factorization through that neighbourhood. The preceding construction then
provides the full fibrewise root datum and rank-one root exponent spaces over
that algebra. These witnesses give exactly the unchanged target conclusion.

The two proposition arguments remain explicit proof obligations. This
conditional theorem proves neither Borel representability nor finite étale
refinement, and does not by itself prove the unconditional target.

The provenance is internal assembly of the published interfaces just named,
`localSplitDataOfFibrewiseMaximalTorus`,
`splitTorus.fibrewiseMaximalBaseChange`, and the published base-change
composition and isomorphism transport results. No new geometric existence
principle is assumed beyond the two explicit proposition arguments.
