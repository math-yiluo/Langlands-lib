# Fibre products along étale morphisms of `G`-spaces are `G`-spaces

`etalePullbackGSpace` proves `EtalePullbackGSpaceStatement` in the original
independent universes for the field, spaces and group. The proof works on the
supplied categorical pullback in `LocalizedCategory`; it does not construct a
pullback or an action.

First, `etale_le_quasiEtale` makes the étale first leg quasi-étale. With the
Hausdorff hypotheses on the two factors installed as instances,
`hasCompactPairPreimages_of_quasiEtale` applies to this pullback. The proof takes
only its Hausdorff conclusion. Independently,
`isContinuousAction_of_isPullback_of_quasiEtale` applies to the same square,
using continuity of the two factor actions and equivariance of both projections.
It gives continuity of the supplied action in the Library's analytic test-triple
sense. These results use smallness of the constructed fibre product along a
quasi-étale leg, not a uniform bound on the size of all affinoid spectra. Neither
application needs the statement's Hausdorff hypothesis on the base.
