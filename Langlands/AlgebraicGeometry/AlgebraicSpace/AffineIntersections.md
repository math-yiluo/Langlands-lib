# Affine intersections for a presheaf with closed diagonal

These internal lemmas support the proof of scheme representability for separated
commutative group algebraic spaces. They concern arbitrary Type (u + 1)-valued
presheaves on schemes over a base S, and require no sheaf or group structure.

The theorem `closedImmersion_pair_of_isPullback` says that an actual represented
fibre product V of charts V1 and V2 maps by a closed immersion to their product
in the slice over S, provided the diagonal of the target presheaf is a
representable closed immersion. The proof identifies this map as a represented
base change of that diagonal. A categorical pullback-cone argument supplies the
diagonal square, and the product comparison for scheme Yoneda identifies its
product with the represented slice product.

If S, V1 and V2 are affine, their slice product is affine: its underlying scheme
is the ordinary scheme fibre product V1 ×_S V2. A closed immersion into that affine
scheme has affine source. This proves
`isAffine_of_isPullback_of_closedDiagonal` for every actual represented fibre
product, without requiring the chart maps to be open.

Finally, `exists_affine_open_intersection` takes two representable open immersions
from affine schemes and constructs a represented fibre product. The preceding
lemma makes its source affine, and the two base-change properties make both
scheme projections open immersions. The affine base hypothesis is explicit; this
file makes no assertion that arbitrary open subschemes of affine schemes are
affine. The results are derived from the Library's representable immersion
predicates and Mathlib's categorical products, pullbacks and affine-morphism API.
