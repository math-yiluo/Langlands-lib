# Affine closed loci of projective tensor equations

This internal derived unit connects `ProjectiveTensorCoefficients` to actual
schemes. For a set I in A tensor_R P, `tensorCoefficientLocus I` is the spectrum
of A modulo its coefficient ideal. `tensorCoefficientLocusι` is its canonical
closed immersion into Spec A. These constructions do not require projectivity.

`factorsThrough_affineQuotient_iff` first packages Mathlib's quotient lift:
for any scheme T, a morphism T to Spec A factors through Spec(A/J) exactly
when the induced homomorphism A to the global sections of T kills J. The
forward implication uses naturality of the global-sections/spectrum
isomorphism; the reverse implication uses `Scheme.Hom.liftQuotient`.

`factorsThrough_tensorCoefficientLocus_iff` applies this to the coefficient
ideal and tests its span generators. Thus factorization through the actual
closed immersion is equivalent to vanishing of every dual contraction on
every test scheme, with no affineness restriction on the test scheme.
For a projective P, `affine_factorsThrough_tensorCoefficientLocus_iff` states
that the morphism Spec B to Spec A induced by any R-algebra map f factors
through the coefficient locus exactly when every selected tensor becomes
zero in B tensor_R P. Neither B nor f has a flatness assumption, and P need
not be finitely generated.

This is the affine coefficient-locus step in the proof of
Conrad–Gabber–Prasad, *Pseudo-reductive Groups*, second edition (2015),
Proposition A.8.10(1), printed pp. 547–549. It does not identify a product
of schemes with an affine tensor spectrum, establish the product-factorization
condition on arbitrary test schemes, glue loci over a nonaffine target, or
descend them along faithfully flat extensions. The three group-scheme
representability targets therefore remain separate obligations.
