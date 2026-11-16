# The general smooth-affine torus Weyl quotient

`smoothAffineTorusWeylQuotient` proves the unchanged Library proposition
`SmoothAffineTorusWeylQuotientStatement.{u}` for every universe `u`.
For an arbitrary scheme `S`, a smooth relatively affine group scheme `G`,
and a closed relative torus `t : T.toGrp ⟶ G`, it constructs actual closed
normalizer and centralizer representatives `n : N ⟶ G` and `z : Z ⟶ G`.
It also constructs a group scheme `W` whose structure map is separated,
quasi-compact and étale, and a flat surjective locally finitely presented
homomorphism `q : N ⟶ W`. On every test scheme `U : Over S` and point
`y : U ⟶ N.X`, the proved kernel condition is exactly

`y ≫ q.hom.hom = 1 ↔ y ≫ n.hom.hom ∈ (torusCentralizer t).carrier U`.

These are the original hypotheses and conclusion. The base need not be
Noetherian or connected; the relative torus rank may vary along an étale
splitting cover. The ambient group need not be reductive, the torus need
not be maximal, and no finiteness of `W → S` is asserted. All subgroup and
kernel identities refer to the published functors on every scheme over `S`,
including all further refinements.

The proof first applies `relativeTorusSmoothNormalizerModel`. This uses the
published closed, locally finitely presented normalizer representative and
the arbitrary-ring diagonalizable normalizer lifting theorem to prove that
its structure map is smooth. The normalizer is relatively affine because
it is closed in `G`. The published `relativeTorusCentralizerModel` supplies
a smooth closed representative `z` of the actual centralizer.

`relativeTorusCentralizerNormalizerInclusion` factors `z` through `n`,
giving `c : Z ⟶ N` with `c ≫ n = z`, and identifies its all-test range with
the preimage of `torusCentralizer t` under `n`. This map is an open
immersion: on a splitting cover of the torus, conjugation rigidity
identifies centralization with the open identity-action locus; open
immersions descend along the cover. The factor `c` is also closed because
`z = c ≫ n` and `n` are closed immersions.

The chosen scheme quotient is
`TorusCentralizerQuotient.homogeneousQuotient t hT n c hcrep hcclosed hZs`.
Its construction takes the actual universal relative Hom family from `T`
to `G` and classifies conjugation by points of `N`. Two such parameters
coincide exactly when their ratio lies in the centralizer preimage.
The published smooth-relation quotient construction applied to this
map gives an actual quotient scheme with smooth surjective projection
and these exact coset fibers. The closed coset relation gives a closed
quotient diagonal by fppf descent, hence separatedness. Quasi-compactness
of the quotient over `S` follows from surjectivity of the projection and
relative affineness of `N`. The construction also retains a
quasi-compact projection and local finite type of the quotient.

The published statement that the torus centralizer is normalized by the
torus normalizer proves normality of `range c`. The actual normalizer
representing property supplies membership of every `N`-point in that
normalizer. The proof then uses the published
`HomogeneousQuotient.groupScheme` and `groupProjection` constructions:
normality descends the group operations to the chosen quotient scheme.
The resulting group projection has the same underlying morphism and is
an fppf quotient with represented kernel `range c`.

`etale_of_open_subgroup_quotient` proves that this quotient is étale over
`S`. The coset relation inclusion is a base change of the open immersion
`c`. Its identification with the pullback of the quotient diagonal
allows descent of openness along the product of the two smooth
surjective projections. Thus the quotient structure map is formally
unramified. Smoothness descends from `N` along the smooth surjective
projection; together, these properties give étaleness. The group
structure preserves the underlying separated, quasi-compact quotient
scheme.

Finally, the represented fppf kernel is `range c`. Rewriting by the
representing equality for `c` identifies that range with
`(torusCentralizer t).comap n`. The published all-test membership
criterion for the actual scheme-theoretic kernel gives exactly the
displayed equivalence, rather than a claim restricted to geometric or
base-valued points.

This is an internal composite proof using the paired constructions
`RelativeNormalizerSmooth`, `CentralizerOpenInNormalizer`,
`HomScheme.SmoothRelativeSourceRepresentability`,
`HomScheme.ConjugationMap`, `CentralizerQuotient`, and
`OpenSubgroupQuotientEtale`, together with the published centralizer and
homogeneous-quotient interfaces. The original-source correspondence is
that of the unchanged
[`SmoothAffineWeylQuotientStatement`](SmoothAffineWeylQuotientStatement.md):
Conrad, *Reductive group schemes* (2014), Theorem 2.3.1,
Proposition 2.1.2 and Lemma 2.2.4. The implemented proof uses actual Hom
representability and the smooth coset relation throughout.
