# Atlas points as localized tuples with overlap equations

This derived unit constructs an O-linear equivalence `overlapPointEquiv`
between the full compatible-family points of a supplied `BasicAtlas` and
one actual nilpotent chart tuple over each canonical localized test algebra,
subject to the actual transition equations on every pairwise overlap. The
inverse is constructed by localization lifts, and both inverse equations
are proved.

## Provenance and scope

Drinfeld, *Coverings of p-adic symmetric regions* (1976), printed p.109
(PDF page 3), paragraph immediately before section 2, permits formal groups
obtained by gluing formal groups over localizations of the base. The registered
source is `drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
The present equivalence is a derived consequence of the localization universal
property and the existing `BasicAtlas` compatibility equations, under that
convention. It is not a separately stated theorem of Drinfeld.

O and R are arbitrary commutative rings with an O-algebra structure on R. The
atlas is supplied on a fixed finite coordinate type in `Type`. All coefficient
test algebras lie in the same universe v as R. The original full-family carrier
has universe v+1; the localized tuple carrier has universe v. The cover may be
infinite. No flatness or injectivity of coefficient maps is assumed. The cover's
span condition and the transition cocycle are not needed for this equivalence:
coefficient naturality of the supplied transitions and the pairwise matching
equations suffice to reconstruct the two defining compatibility conditions.

This unit describes points of the given atlas. It does not construct a global
coordinate law or assert that the tuples come from a tuple over A. It does not
prove refinement invariance, independence of presentations, a sheaf condition
for arbitrary covers, a comparison of formal schemes, order linearity, moduli
representability, framing, heights or level structures.

## Universal localized overlaps

`localMap_ext` cancels the structural map A → A[1/a] in comparisons of
R-algebra maps out of A[1/a], using `IsLocalization.ringHom_ext` and then
extensionality of algebra and categorical morphisms. `testFactor_comp` uses
this uniqueness and `localizationMap_testFactor` to prove that the
localization factor of a chart test commutes with a further coefficient map.

For charts a and b, `overlapAlgebra A a b` is the actual localization
A[1/(a_A b_A)], where a_A and b_A denote their images in A. `overlapMap` is
its structural map as an R-algebra. `overlapUnitLeft` and `overlapUnitRight`
follow from invertibility of the product and the scalar-tower identity.
`overlapFromLeft` and `overlapFromRight` are the actual localization lifts
from A[1/a_A] and A[1/b_A] to that joint localization.

For any R-algebra map φ : A → B with both generators invertible in B,
`overlapFactor` is the unique localization lift from the joint localization
to B. `overlapMap_factor` checks the lift on A. Uniqueness out of the
single-generator localizations proves `overlapFromLeft_factor` and
`overlapFromRight_factor`: restricting along either side and then applying
the joint lift equals that chart test's direct localization factor.

## The explicit solution module

`LocalizedFamily A` is the dependent product of the actual O-modules
`ChartPoint (localAlgebra A a) a (localUnit A a)`. Each carrier is the existing
nilpotent tuple carrier of the actual localized formal chart law. Its addition
and scalar action come from that law.

`OverlapCompatible z` requires, for every ordered chart pair a,b, that the
left tuple restricted to the joint localization and changed to chart b by
`transitionPoints` equals the right tuple restricted there. The two restriction
maps are the actual `pointMap` maps along `overlapFromLeft` and
`overlapFromRight`. These equations define `overlapSubmodule`; closure under
zero, addition and O-scalars uses linearity of the restrictions and transition.
`OverlapPoint A` is this submodule.

`localizedCoordinates_compatible` applies `component_from_localTest` twice
at the joint overlap test. The chart-change compatibility of the original
full family then gives the pairwise equation. `toOverlapPoints` is the
existing canonical coordinate evaluation with this image condition attached;
it is O-linear component by component.

## Reconstruction and the inverse equations

`familyOfOverlap z` defines the component at an arbitrary chart test t by
applying `pointMap` along `testFactor t` to the prescribed localized tuple
z(t.chart). Its coefficient naturality follows from `testFactor_comp` and
`pointMap_comp`. For its chart-change equation, map z's pairwise equation
along `overlapFactor` into the test algebra. The naturality of the actual
transition moves this coefficient map through the chart change. The two
factor identities then identify both sides with the directly reconstructed
test components. This proves `familyOfOverlap_compatible`.

`fromOverlapPoints` packages that family and its proved compatibility as an
O-linear map to full atlas points. Its linearity is the linearity of each
actual chart-point coefficient map. `testFactor_localTest` proves that the
localization factor at a canonical local test is the identity, by uniqueness
of maps out of the localization.

`fromOverlapPoints_toOverlapPoints` uses `component_from_localTest` at every
test: reconstruction of a full family from its canonical components is the
original family. `toOverlapPoints_fromOverlapPoints` uses
`testFactor_localTest` and `pointMap_id`: the reconstructed canonical tuples
are exactly the prescribed tuples. `overlapPointEquiv` assembles these maps
and both inverse equations into the claimed O-linear equivalence. Its two
application lemmas expose the canonical evaluation and the explicit
localization-lift inverse.
