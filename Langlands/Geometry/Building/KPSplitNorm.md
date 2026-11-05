# Bounded norms on split tori

This internal reduction starts from scalar unit-norm surjectivity for a finite
Galois field extension. It proves that every point in the character-valuation
kernel of a split torus is a norm of a point in the corresponding extension-field
kernel. No scalar arithmetic surjectivity assertion is proved in this module.

The multiplicative-group argument uses the actual base-change isomorphism of
Gm, its field-unit point equivalence, and the published comparison of its
rational norm with the field norm. For a general split torus, a chosen split
isomorphism expresses a bounded point as a product of coordinate cocharacter
values. Each coordinate admits a bounded scalar norm lift; functoriality of
the torus norm subgroup then puts their product in the norm subgroup.

When the valuations are compatible and the extension valuation is Galois
invariant, `boundedRationalNorm` restricts the actual rational norm to the two
character-valuation kernels. Under scalar unit-norm surjectivity it is surjective
for any affine split torus.

This implements the split-torus reduction in Kaletha–Prasad, *Bruhat–Tits Theory:
A New Approach* (2023), Lemma 2.5.12, printed pp.89–90 (PDF pp.120–121). The
finite-Galois, scalar-surjectivity and valuation assumptions are explicit. The
module does not assert splitting-field independence or the final zero-subgroup
independence theorem.
