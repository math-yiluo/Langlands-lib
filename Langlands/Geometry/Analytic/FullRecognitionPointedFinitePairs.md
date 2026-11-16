# Pointed finite full-recognition chart pairs

For a strong map between the local-domain enlargements of two affinoid atlas
presentations, `HasFiniteFullRecognitionPairAt g y` asserts the existence of
recognized affinoid subsets `V` and `W`, an admissible bounded pullback from
`W` to `V`, and a spectral point `s` of `V` whose chart image is the prescribed
point `y`, such that this pullback is a finite Banach algebra map.

`HasFinitePiecesAt.exists_pointed_fullRecognitionPair` selects such a pair
from the published finite-pieces condition and retains its additional
pointwise property `Q`. The finite family of target subsets has union a
neighborhood of the image point. Membership of the point in that union selects
one target subset `W`. The finite-over condition supplies a source subset `V`
whose locus is the intersection of the source neighborhood and the inverse
image of `W`. That locus contains `y`. The equality between the recognized
subset's locus and its chart range then supplies `s`, and the original
finite-pieces condition supplies `Q` at this same `s`.

`IsFiniteAt.hasFiniteFullRecognitionPairAt` applies the published
`hasFinitePiecesAt_of_isFiniteOver` to the constantly true pointwise property
and then uses this selection lemma.

This is an internal deduction from the Library's existing full-recognition
definitions and neighborhood theorem. It makes no new identification with
external analytic geometry. The ground field is complete and ultrametric,
and the presentation and coefficient universes are as in the imported
`IsFiniteAt` definition. No Hausdorff or nontrivial-valuation condition is
added. These lemmas select finite local pieces; they do not construct an
all-chart field-valued point or prove the étale site point axioms.
