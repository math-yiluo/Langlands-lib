# Arbitrary tori are central in nilpotent groups

Author: Worker 1487.

This internal construction concerns any smooth connected affine group scheme
with the existing geometric nilpotence predicate, over an arbitrary field in
universe `u`. Every homomorphism from a torus is central on every relative test
scheme. Its all-test torus centralizer is the whole group. The construction
`IsNilpotentGroupScheme.torusCentralizerIso` identifies any group scheme
representing that centralizer with the ambient group. Its forward map is the
original representing inclusion. The torus homomorphism need not be injective
or closed, and the torus need not split over the base field.

First, a uniform all-test lower-central bound is transported through the actual
multiplicative point equivalence for base change. Mapping the lower central
series by the inverse equivalence preserves its terms, sends the full subgroup
to the full subgroup and the trivial subgroup to the trivial subgroup. Thus the
same bound holds over every field extension. Applying this to geometric points
gives geometric nilpotence. The existing uniform bound for a smooth connected
affine geometrically nilpotent group therefore proves stability of its geometric
nilpotence under every field extension, including inseparable extensions.

Choose the splitting extension from the actual torus predicate. Smoothness and
affineness persist under pullback; connectedness follows from the existing
geometric connectedness theorem for smooth connected affine groups. The split
torus centrality theorem applies over this extension. Since a field extension
is flat and surjective on spectra, the published all-test fpqc reflection of
centrality descends this conclusion. The centralizer equality and its actual
representing isomorphism then follow from centrality and the existing full
subgroup isomorphism construction.

This is a derivation from the Library's all-test nilpotence bound, actual point
base-change equivalence, split torus centrality and fpqc reflection, rather than
a new translation of an external result. Construction of a maximal torus and
unipotence of its quotient remain separate obligations.
