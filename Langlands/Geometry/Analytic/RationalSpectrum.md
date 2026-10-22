# Proof of spectrum identification for a rational presentation

Author: Worker 36.

`Langlands.Analytic.RationalPresentation.spectrumIdentification` proves
`SpectrumIdentificationStatement`. The actual rational quotient and
base map are imported from RationalPresentation, and the explicit
fraction subalgebra is imported from RationalSpectrum.Definitions.

At a point x of the rational norm locus, the denominator is nonzero by
the proved unit-ideal argument. Its image in the constructed completed
residue field H(x) is therefore nonzero. The fractions f_j(x)/g(x) have
norm at most one and hence bounded monomials. Evaluation and quotient
descent give a bounded map from the rational quotient to H(x). Pulling
back its field norm constructs a point over x. The restriction formula
and exact residue norm evaluation show that this lift maps back to x.
Together with the forward inclusion this identifies the exact spectrum
image under the explicit unit-ideal hypothesis.

For density, every old coordinate belongs to the fraction subalgebra
with exponent zero, and every new coordinate belongs with exponent one
by g Y_j = f_j. Its topological closure is a closed subalgebra containing
all coordinates and scalars, hence every projected Tate monomial.
Convergent monomial expansions and surjectivity of the quotient projection
show that the closure is the whole quotient. This argument does not
require the unit-ideal condition or denominator invertibility.

For injectivity, two spectrum points with the same base restriction
agree on the fraction subalgebra by cancelling the nonzero seminorm of
a power of g. Here the unit-ideal condition is used to prove that
nonvanishing. The seminorms are continuous, as shown using their actual
completed residue maps; density extends their equality to the whole
quotient. Compactness and Hausdorffness give a closed embedding. The
closing theorem assembles the unconditional density clause and the two
conditional spectrum clauses.

No argument splits on the variable counts n and m, on the relation set
S, on whether the quotient is the zero ring, or on whether the absolute
value of K is trivial. The closing theorem is proved for every instance
of the target's quantifiers, including empty fraction tuples, zero
quotients and trivially valued coefficient fields.

The target and definition Markdown record the exact original-source
context and the derived scope. This proof uses the constructed residue
fields, bounded quotient extensions and Tate monomial expansions. It
does not prove absence of common zeros implies the unit ideal, the full
analytic-domain factorization property, a structure sheaf, an atlas,
or results for arbitrary radii.
