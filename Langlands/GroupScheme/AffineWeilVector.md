# Vector coordinates for finite free affine Weil restriction

This derived construction takes a finite projective commutative algebra
`A → B` and a specified basis `b : Basis (Fin n) A B`. It identifies the
actual affine Weil restriction of the additive vector group of dimension
`m` over `B` with the additive vector group of dimension `m * n` over `A`.
All rings have arbitrary common universe `u`. In particular, `B` may have
nilpotents; no field or separability hypothesis is imposed.

`tensorCoordinateEquiv` sends an array `x` to `∑ j, b j ⊗ x j`.
Its inverse reads the basis coordinates of a tensor. Both directions
commute with every map of coefficient algebras. `tensorVectorEquiv` applies
this comparison to each vector coordinate and flattens the two finite
indices using `finProdFinEquiv`.

`vectorAffineCoordinates` composes the published multiplicative affine
point comparison for the original vector group with these tensor basis
coordinates. `vectorCoordinates` then applies the published relative
global-sections comparison to every scheme test of the actual restriction.
`vectorCoordinates_naturality` records compatibility with pullback of
global functions. Yoneda recovery produces `vectorIso`, an isomorphism
of the actual group schemes with their additive group laws.

`vector_isVectorGroupOfDimension` records the all-test vector-group
predicate over any base ring. Over a field, `vector_properties` applies
the published vector-group geometry results to prove smoothness,
connectedness, and representation-theoretic unipotence. Dimension zero
is included.

The provenance is the finite free coordinate calculation underlying the
restriction-of-scalars assembly in Kaletha–Prasad, *Bruhat–Tits theory:
a new approach* (2023), Proposition C.5.1, printed pp.703–704 / PDF
pp.734–735. The basis and all-test coordinate isomorphisms are derived
internal constructions from the published tensor-product and affine Weil
APIs; the source does not state this explicit coordinate isomorphism.
This unit does not construct a special-fibre comparison or prove the
root-model identification in Lemma C.5.3.
