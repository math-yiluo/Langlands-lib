# The ideal of a cubic embedding from its labelled torsion points

`Datum.IsCubicEmbedding.polynomialTwistIso` transports the actual twist
isomorphism of a supplied relative cubic embedding to polynomial
projective space over the field. It uses the isomorphism of projective
models over the affine base and its comparison of their degree-one twists.

For positive `g, d`, over an algebraically closed field with `n ≠ 0`,
`Datum.IsCubicEmbedding.homogeneousVanishes_iff_torsion` applies to each
homogeneous form `F` of degree `t` with `6^g d g! t < n²`. The form vanishes
in the scheme-theoretic kernel of the polynomial embedding if and only if
it lies in the homogeneous prime of the image of every labelled torsion
point. The proof pulls its section `F / 1` back and uses the tensor-power
and twist comparisons to make it a section of the `t`-th cubic power.
The inverse image of `D₊(F)` is exactly the generation open of that section.
If every labelled torsion point misses the open, the cubic-power count
forces it to be empty, so the section is zero by reducedness of the
abelian variety. The scheme-theoretic vanishing lemma then gives the kernel
criterion. The converse follows from the same lemma and the empty
generation open of zero. This proof includes degree zero.

`exists_cubicEmbedding_ker_eq_of_torsion` fixes `g,d,m` in a universe and
finds a bound `N` which works for all prerequisites, levels, fields and
data therein, for *supplied* cubic embeddings into the same relative
projective space. Equality of the actual labelled projective point maps
implies equality of the two kernel ideal sheaves. The cutoff from the
fixed Hilbert-polynomial piece gives one equation degree bound `D` for both
embeddings. Choosing `N = (6^g d g!) D + 1` makes the level-square
inequality hold for every tested degree. Thus both ideals have identical
vanishing tests in the generating degrees; equality on all charts follows.
The induced isomorphism of the sources over the polynomial projective
space transports equality of kernels back to the relative model.

This is a derived consequence of the Library's fixed-Hilbert-piece bound,
its actual twist comparisons, and the power-section adaptation of the
Bézout argument for GIT Proposition 7.7. The statement concerns equality
of ideals, not just of their supports. It does not produce compatible
embeddings from evaluation configurations, recover the abelian group law
or polarization, or prove the full `TorsionConfigurationDeterminationStatement`.
