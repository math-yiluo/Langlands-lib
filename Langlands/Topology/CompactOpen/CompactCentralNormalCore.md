# Open normal cores for compact central quotients

Let `G` be a topological group with compact `G ⧸ Subgroup.center G`.
For an open subgroup `K`, `Langlands.compactCentralNormalCore K` is the
normal core of `K` bundled as an open subgroup. Conjugation factors through
the central quotient in its first argument. The action of that quotient
on `G` is continuous because it becomes ordinary continuous conjugation
after precomposition with the open quotient map times the identity.
The inverse image of `K` under the action contains the product
`(G ⧸ Subgroup.center G) × {1}`. The tube lemma gives an identity
neighborhood whose elements are conjugated into `K` by all of `G`.
Thus the normal core contains an identity neighborhood and is open.

When `G` is also weakly locally compact and nonarchimedean,
`Langlands.exists_compactOpenNormalSubgroup_subset` takes a compact open
subgroup inside a given identity neighborhood using
`Langlands.compactOpenSubgroupBasis`. Its normal core is closed, so it
is compact and still lies in the neighborhood.

For any open subgroup `K` containing the center,
`Langlands.finiteIndex_of_open_of_center_le` uses the continuous surjection
from the compact central quotient onto the discrete coset space `G ⧸ K`.
The coset space is compact and discrete, hence finite.
