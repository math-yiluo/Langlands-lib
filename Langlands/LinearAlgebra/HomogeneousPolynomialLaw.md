# Homogeneous polynomial laws on a module

`HasHomogeneousPolynomialLaw delta d` means that on every finite tuple of
vectors the function delta is represented by a homogeneous multivariate
polynomial of total degree d. It chooses no basis and places no finite dimensionality assumption on the module. This is an internal interface for
the separate, unproved geometric degree-polynomial assertion.

`homogeneous_eval_smul` proves scalar homogeneity of evaluation by expanding a
homogeneous polynomial into supported monomials. The sum of each monomial's
exponents is d, so scaling every input by c multiplies its value by c^d.
The unary restriction of the polynomial-law predicate therefore gives
`delta(c smul a)=c^d*delta(a)`. A law of positive degree vanishes at zero.
Precomposition with a linear map preserves the law by using the representing
polynomial for the tuple of images.

`homogeneousLaw_eq_of_integer_lattice` states uniqueness over the rationals.
Suppose every vector a has a nonzero natural-number denominator n with n*a
in the image of an additive map from an integral group. Two laws of the same
degree that agree on that image then agree everywhere: scalar homogeneity
compares their values after multiplying by n, and cancellation of the nonzero
rational scalar n^d gives equality at a. All denominator and polynomial-law
hypotheses are explicit.

The provenance is internal. These are elementary consequences of the finite
monomial expansion, homogeneous total degree, linearity, and rational scalar
cancellation. No actual geometric polynomiality, Tate determinant comparison,
or trace rationality is asserted or proved.
