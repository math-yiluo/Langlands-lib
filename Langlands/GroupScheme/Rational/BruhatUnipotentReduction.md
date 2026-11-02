# Unipotent reduction of rational Bruhat separation

This internal proof assembly implements the final paragraph of Borel–Tits,
*Groupes réductifs* (1965), §5.15, printed page 101 (PDF page 48 with
one-based numbering). It uses the Library's actual rational-point dynamic
Levi decompositions, rather than an assumed Tits system or an assumed
surjectivity statement for a quotient morphism.

`HasUnipotentNormalizerSeparation i ν` is the intermediate assertion that,
for normalizing points `n,n'` and dynamic unipotent points `u,v`,
`n' = u * n * v` implies `n' = n`. This file does not prove that geometric
assertion. It is not added to the hypotheses of `RationalBruhatStatement`.

`rationalLevi_eq_centralizerPoints_of_eq` evaluates an assumed equality of
the dynamic centralizer with the whole-torus centralizer at the base scheme.

`relativeWeyl_eq_of_parabolic_mul_of_unipotent_separation` assumes that
centralizer identity and unipotent normalizer separation. From
`n' = p * n * q` it uses the published decompositions to write
`p = u * a` and `q = b * v`, with `a,b` in the dynamic Levi. The centralizer
identity puts `a,b` in the whole-torus centralizer, hence also the normalizer.
Unipotent separation gives `n' = a * n * b`. Both centralizer factors vanish
in the actual quotient `N(k)/Z(k)`, proving equality of relative Weyl classes.

`hasRationalBruhatDecomposition_of_unipotent_covering_and_separation` combines
this argument with an assumed covering `G(k) = U(k) N(k) U(k)`. The inclusion
of the actual dynamic unipotent subgroup in the actual dynamic parabolic
gives parabolic covering. The converse implication for normalizer classes
uses the whole-torus centralizer's inclusion in the dynamic Levi and then
the parabolic.

The statements hold over every field for an affine group scheme. Maximality,
genericity, and reductivity are unnecessary for these conditional reductions.
The full theorem still requires the centralizer identity, geometric
unipotent covering, and geometric unipotent normalizer separation at its
published hypotheses. The original source explains the mathematical passage;
the implemented proof uses the Library's unique Levi factorizations and the
group-quotient API.
