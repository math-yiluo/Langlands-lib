# Comparing a maximal torus with a torus centralizer

Author: Worker 1479.

This internal construction works over every field `k : Type u`. Let
`i : T.toGrp → G` be a supplied maximal torus and let
`a : A.toGrp → G` be a homomorphism from any commutative group scheme.
Retain the supplied map `f : A.toGrp → T.toGrp` and equation `f ≫ i = a`.
If a closed homomorphism `j : C → G` represents `torusCentralizer a`
on every test scheme, and `C` is a torus, the construction compares `T`
directly with that representative.

`IsMaximalTorus.isoTorusCentralizer` constructs an actual group-scheme
isomorphism `T.toGrp ≅ C`. Its forward map is the published `factorHom`
of the original `i` through `j`. Indeed, commutativity of `T` and the
supplied factorization imply that the full range of `i` centralizes `a`;
this is `range_le_torusCentralizer_of_factor`. Representability therefore
provides `q : T.toGrp → C` with `q ≫ j = i`.
Since `j` is closed, `IsMaximalTorus.of_comp` makes `q` a maximal torus
of `C`. The published `IsMaximalTorus.isIso_of_torus` then makes `q`
an isomorphism.

`isoTorusCentralizer_hom_comp` proves that the forward map followed
by `j` is exactly `i`. `isoTorusCentralizer_unique` proves uniqueness
of an isomorphism with that compatibility by cancellation against the
monomorphism underlying the representative.

`IsMaximalTorus.isRepresentedBy_torusCentralizer_of_isTorus` proves
that the original supplied `i` represents `torusCentralizer a`.
Closedness of `i` supplies the required monomorphism. Precomposition
with the comparison isomorphism does not change a subgroup functor's
range, so `range i = range j = torusCentralizer a`. This equality
uses every test scheme, including nonreduced tests, and the centralizer
definition tests commutation after every refinement.

The provenance is intrinsic: these constructions combine the imported
all-test factorization, closed-subgroup maximality and maximal-torus
comparison results. They impose no reductivity, quasi-splitness, splitness
or maximal splitness assumption. They prove no existence of a torus
centralizer and do not prove `QuasiSplitMaximalTorusCentralizerStatement`.
