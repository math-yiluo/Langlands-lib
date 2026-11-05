# Actual coordinate reduction for additive polynomial kernels

This module implements the coordinate reduction in Conrad–Gabber–Prasad,
*Pseudo-reductive groups*, second edition (2015), Lemma B.1.7 and its proof,
printed pp.563–564 (one-based PDF pp.589–590). The coefficient-extension
corollary also uses Lemmas B.1.8–B.1.9, printed pp.564–565 (one-based
PDF pp.590–591), through the preceding polynomial-curve Galois theorem.
The all-field formulation, including characteristic zero, is derived from the
previous exponential-characteristic degree reduction and actual polynomial
shear isomorphisms.

`HasPolynomialKernelZeroCoordinate f hf` asserts the existence of an additive
row `g`, a proof `hg` of its universal polynomial additivity, and an actual
standard vector-group isomorphism `e` such that
`e.hom ≫ polynomialRow f hf = polynomialRow g hg` and `g j = 0` for some
coordinate `j`. Both sides of this equation are actual group-scheme
homomorphisms. The actual row morphisms were constructed by natural polynomial
evaluation on the global functions of every relative scheme test.

`hasPolynomialKernelZeroCoordinate_of_pointed` constructs these data from a
nonzero polynomial kernel curve whose coordinate constants are zero. The
implemented proof uses strong induction on the sum of the row's polynomial
natural degrees. If an entry of the row is already zero, it uses the identity
coordinate isomorphism. Otherwise the kernel relation gives a nontrivial zero
of the principal part. The previous degree-reducing shear then strictly lowers
one entry's degree and preserves the other entries.

The inverse shear transports the pointed nonzero curve into the transformed
kernel. Its two inverse polynomial identities preserve nonzeroness and the
kernel relation. The induction hypothesis supplies an actual isomorphism for
the smaller row. Composing it with the current actual shear isomorphism gives
the required ambient isomorphism; the actual row-transformation equality proves
the displayed equality of morphisms. Each degree step is finite, and the proof
uses no infinitude or perfectness assumption on the field.

`hasPolynomialKernelZeroCoordinate_of_nonconstant` first replaces an arbitrary
nonconstant polynomial curve by a nonzero additive one using the preceding
polynomial theorem, then applies the pointed construction.
`hasPolynomialKernelZeroCoordinate_of_not_hasConstantAffineLineMaps` uses the
existing extraction of a nonconstant polynomial curve from an actual failure
of affine-line constancy. It therefore starts with actual affine-line scheme
morphisms and returns the actual ambient isomorphism, over every field.

`hasPolynomialKernelZeroCoordinate_of_nonconstant_galois` gives the same
coordinate change over the original field when a nonconstant polynomial curve
is initially given over an algebraic Galois extension. It descends polynomial
curve existence using the preceding Galois theorem and then applies the
construction over the original field. The extension field has an independent
universe; the theorem does not assert a cross-universe base-change isomorphism.

The conclusion supplies some zero coordinate. The original lemma selects the
first coordinate by a final permutation; that permutation is not included
here. This unit does not yet identify the kernel with a product, produce the
complete vector-factor decomposition, or prove the arbitrary unipotent-group
woundness criterion. No structural presentation or additional theorem premise
is assumed for an arbitrary group.
