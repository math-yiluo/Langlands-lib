# Common maximal split tori and rational Bruhat covering

Author: Worker 1262.

This internal reduction constructs actual scheme normalizer witnesses from
conjugacies of torus embeddings. It does not prove the geometric structural
statements on minimal parabolics.

`innerIso_hom_comp` proves naturality of inner automorphisms on every test
scheme by the group-homomorphism laws on points.

`normalizerPointOfConjugacySquare` takes two actual torus-source isomorphisms
and equations saying that conjugation by `p` and by `g*q` takes the original
torus to the same torus. It constructs the point `p⁻¹*g*q` in the actual
`normalizerPoints i`. The source automorphism is `e'` followed by `e⁻¹`,
viewed as an automorphism of the commutative group scheme. Its defining
equation follows by composing with inverse inner conjugation by `p`.
Consequently this construction concerns the scheme torus, even when the
field is finite. It never replaces normalization with preservation of the
finite group of rational torus points.
