# Common coordinate domains and local root products

`HasLocalRootClearing` records a finite set of allowed root forms, a common power,
and a common neighborhood of a coordinate center. On a set dense in that
neighborhood, the product times each scalar evaluation agrees with a holomorphic
function on the neighborhood.

`exists_meromorphicInCoordinatesOn_of_local_rootClearing` uses local meromorphic
data and this clearing property in a single linear coordinate system. The existing
coordinate gluing theorem supplies one open dense holomorphy domain for all
scalar evaluations. Intersecting that domain with the locally dense agreement
set is dense in the part of the chosen neighborhood on which the original
family is holomorphic. The power of the root product is entire, by finite products
and powers of the centered linear forms. Continuity extends the local agreement
identity to the entire intersection of the neighborhood and holomorphy domain.

A change of coordinates is a continuous complex-linear equivalence between the
two coordinate spaces. Pulling back the neighborhood and each extension along
it preserves holomorphy and the root-form identity, including the center.
The image of the one coordinate holomorphy domain is the common parameter domain
in the conclusion.

This derived gluing step applies to the uniform local root products in
Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*, §8.6,
Corollary, p. 226. The local meromorphic data and local root clearing are premises.
