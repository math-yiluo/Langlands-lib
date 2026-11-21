# Galois descent of characters of affine group schemes

`Langlands.GroupScheme.AffineCharacterGaloisDescentStatement.{u}` is the
proposition that canonical scalar extension identifies the characters of an
affine group scheme over a field with the fixed characters after a Galois
extension.

Take fields `k K : Type u` with `Algebra k K` and `IsGalois k K`, allowing
infinite degree. The group `G : GroupScheme (Spec (CommRingCat.of k))` has
affine structure morphism `G.X.hom`. This includes group schemes of arbitrary
type with either commutative or noncommutative group law.

The additive integral module `rationalCharacters G` consists of actual
homomorphisms from `G` to the multiplicative group. Write `b` for the scheme
map `algebraBaseMap k K` from `Spec K` to `Spec k`. The map called `extend`
in the statement sends a character to its pullback along `b`, composed with
`(Gm.baseChangeIso b).hom`. Its codomain is the character module of the
actual pullback group scheme. The action
`rationalCharacters.galoisRepresentation k K G` on this codomain sends
`σ : K ≃ₐ[k] K` to the transport of characters along `Spec σ` using the
canonical descent isomorphism for `G`.

The first assertion gives injectivity of `extend`. The second says that
its image as an integral submodule equals the submodule of elements fixed
by every `σ`. Together they give a unique character over `k` whose canonical
scalar extension is the supplied fixed homomorphism over `K`.

Milne, *Algebraic Groups* (2017), §12.g, printed p. 239 (PDF p. 255), gives
the formula identifying the characters over `k` with the
`Gal(kˢ/k)`-fixed characters over the separable closure `kˢ`. Definition 1.1
and its preamble, printed p. 6 (PDF p. 22), give the finite-type convention.
The opening of Chapter 12 and §12.a, printed p. 230 (PDF p. 246), give
affineness and the direction of the character homomorphism. On the groups
in that formula, taking `K = SeparableClosure k` recovers Milne's assertion.
The proposition extends it to arbitrary Galois extensions and affine group
schemes of arbitrary type. The registered source
`milne-2017-algebraic-groups` has SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
