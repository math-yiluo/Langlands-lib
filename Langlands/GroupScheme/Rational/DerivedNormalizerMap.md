# Original normalizer images through a supplied central torus product

Authors: Worker 27 and Worker 1631. The construction uses Worker 1631's
supplied central-product interface and the existing maximal split-torus
and normalizer-lifting infrastructure.

Over a field `k : Type u`, let `d : D ⟶ G` be a group-scheme homomorphism.
Let `T`, `A` and `S` be commutative group schemes with maps
`e : T ⟶ S`, `c : A ⟶ S`, `j : T.toGrp ⟶ D` and `i : S.toGrp ⟶ G`.
Assume that `T` and `A` are split tori, `i` is a maximal split torus, and

`j ≫ d = CommGroupScheme.groupHom e ≫ i`.

The product homomorphism of `e` and `c` is assumed flat and surjective
on schemes, and `CommGroupScheme.groupHom c ≫ i` is central in `G`.
The ambient map `d` need not be monomorphic, surjective or a central
isogeny. No reductivity assumption on `G` is used in this construction.

The definition `DerivedNormalizerMap.normalizerPointsHom` constructs

`normalizerPoints j →* normalizerPoints i`.

Its forward map is the literal rational-point map `rationalPoints.map d`
restricted to these normalizers. The theorem `normalizerPointsHom_coe`
proves this formula by reflexivity. The preservation of the identity and
multiplication comes from the original rational-point homomorphism.

The substantive lemma `map_mem_normalizerPoints` proves the required
membership. For a source normalizer point `n`, choose its actual torus
automorphism `σ` of `T`. Write `g = d(n)` and let `a` be the embedding `i`
followed by inner conjugation by `g`. Naturality of inner automorphisms
identifies the retained component of `a` with the component `σ ≫ e`
inside `S`. Inner conjugation fixes the central component `c ≫ i`.

Consequently, the original product `p : T × A → S`, the product `q` of
`σ ≫ e` and `c`, the embedding `i`, and the conjugated embedding `a` form
the commuting square `q ≫ i = p ≫ a`. The product is a morphism between
affine split tori and hence quasi-compact. With its assumed flatness and
surjectivity it is an effective epimorphism of schemes. The embedding
`i` is a closed immersion, hence monomorphic. The square therefore
has a scheme lift `S → S`.

The private helper `factorHom_of_effectiveEpi` turns this lift into an
actual group-scheme homomorphism `b` satisfying `b ≫ i = a`. It checks
identity and multiplication after postcomposition with the monomorphism
`i`, then uses the original all-test-point representability construction
for group homomorphisms. Since the conjugate of a maximal split torus is
again maximal, the factor `b` is an isomorphism. This is precisely the
torus automorphism witnessing `g ∈ normalizerPoints i`.

The other private helper checks that postcomposition of the actual product
homomorphism is the product of the postcomposed factors, by evaluating
on every test scheme.

This is an internal descent and maximality construction. In its intended
derived-group application, the derived inclusion and the structural tori
and product are still supplied. The module does not construct those
objects, a source apartment, action equivariance on that apartment, or the
final affine-Weyl normalizer image.
