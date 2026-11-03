# The actual affine commutator image

This is internal infrastructure for CGP, *Pseudo-reductive Groups*, second
edition (2015), Lemma 3.3.4 and Proposition 3.3.5, printed pp.108–109 /
PDF pp.134–135, registered as `conrad-gabber-prasad-2015-pseudo-reductive`.
The implementation uses the range of the actual affine commutator pullback.
It supplies the closed image and actual scheme factorization needed before
studying its weights. It does not assert any smoothness, integrality, weight
bound, or generated-subgroup theorem.

For affine group schemes H, K, G over any commutative ring R and homomorphisms
i:H→G and j:K→G, `tensorPresentation` identifies the spectrum of
O(H) tensor O(K) with the actual product H times K. It uses preservation
of products by `algSpec` and the Library's chosen affine presentations.
Its map is explicitly the pair of independent generic points.

`imageAlgebra i j` is the range of the already constructed commutator
pullback O(G)→O(H) tensor O(K). Its quotient map from O(G) is surjective
and its map to the tensor algebra is injective. Taking the actual relative
spectrum gives `imageScheme`, and surjectivity of the coordinate quotient
proves that `imageInclusion` into G is a closed immersion.

`imageFactor` factors the actual scheme commutator morphism through that
closed image. The proof compares coordinate maps and then uses the tensor
presentation isomorphism. `imageFactor_apply` evaluates the factorization on
every test scheme, including nonreduced tests.

`commutatorHom_equivariant` proves the two-input equivariance formula when
actions on H, K, and G intertwine the two inclusions. This uses multiplication
and inverse compatibility of the actual automorphic action. It makes no
assumption about a subsequently constructed action on the image.
