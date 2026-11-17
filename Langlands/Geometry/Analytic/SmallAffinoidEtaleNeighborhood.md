# The actual open étale part of a finite small affinoid map

This internal adapter restricts the actual small-spectrum map of a finite
Banach bounded map to its open pointwise étale locus. The field and ambient
space universes are independent. The finite Banach pushout and finite tensor
comparison propositions remain explicit premises for the étaleness results.
No étaleness premise is imposed outside the locus. The unrestricted analytic
étale-site lifting statement is not established here.

`canonicalGlobalChart_chart_heq` recovers the original small-spectrum chart
function through both saturation steps. Together with the existing complete
bounded pullback recovery, algebra-equality elimination transfers any chosen
pointwise étale point to the corresponding canonical global chart point.
The canonical chart has global range and is an embedding, hence is a
homeomorphism. The open pointwise étale locus of its finite bounded pullback
therefore has open image in the actual small space. The all-pieces theorem
for global finite chart pairs proves
`canonicalMap_isEtaleAtAllPieces_of_pointwise` at the original point.

`etaleOpenSet` is the image of the original bounded map's pointwise étale
locus under the small-spectrum homeomorphism. It is open by `AffinoidEtaleLocus`,
since a finite Banach map is of finite type. `etaleOpenSpace` is the actual
analytic open domain with that carrier, and `etaleOpenMap` is its canonical
inclusion followed by the unchanged original small-spectrum map.

To prove `etaleOpenMap_etale`, the published open-domain inclusion theorem
and the exact comparison between localized and canonical strong étaleness
make the inclusion's canonical extension étale over all pieces. At every
source point its image lies in the original pointwise étale locus, where
the preceding local result applies to the canonical extension of the original
map. Pointwise composition over all pieces and functoriality of saturation
prove canonical strong étaleness of the restricted map. The existing comparison
then gives the exact localized predicate used by the analytic étale site.
