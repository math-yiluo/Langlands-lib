# A common splitting field for compatible centralizer tori

This internal construction retains the actual rational compatible torus of
`TorusCentralizerRationalModel` and chooses one finite Galois extension splitting
both that torus and a supplied actual quotient torus. All fields and group schemes
remain in the arbitrary universe `u`.

`TorusCentralizerFiniteGaloisModel a j Q` stores the rational model, a
`TorusCommonFiniteGaloisSplittingData` for its torus and `Q`, and maximality of the
two actual base-changed torus maps into the ambient group and centralizer.
The splitting data provide the field, algebra, finite dimensionality, Galoisness
and both splitness proofs.

`TorusCentralizerRationalModel.finiteGaloisModel` keeps a supplied rational model.
It assumes that the ambient group and centralizer are smooth and affine and that
`Q` is a torus. It also takes the published proposition
`MaximalTorusBaseChangeStatement` as an explicit input: the common-field
construction supplies splitness, while that separate input supplies maximality
ascent for each of the two retained torus maps.

`torusCentralizerFiniteGaloisModel` first constructs the rational model from a
closed split subtorus and its represented centralizer, and then applies this
common-field construction. It additionally uses local finite type of the ambient
group, as required by the rational maximal-torus extension construction.

`composite_maximal` rewrites the ambient torus map as the actual composite
through the centralizer. The two connected-reductivity lemmas apply the published
arbitrary-field extension theorem to the actual scalar extensions over the
chosen field.

The provenance is an internal composition of rational maximal-torus extension,
common finite Galois splitting of two actual tori, maximality ascent supplied by
its named proposition, and connected-reductivity under field extension. No new
literature theorem is asserted. This pair does not construct root data,
compatible derived tori, cocenter character comparisons or based Galois
corrections, and does not prove the final Levi cocenter root-model proposition.
