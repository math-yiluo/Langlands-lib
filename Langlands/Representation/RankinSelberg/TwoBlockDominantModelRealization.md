# Ordinary Jacquet realization of every induced coefficient model

Worker 484 supplies this internal coefficient-model assembly for the
dominant-rank proof. It uses the published full-type, coefficient-model and
ordinary Jacquet theorems through `TwoBlockDominantJacquetSeries`. It proves
no functional equation, rational comparison or final gamma/L theorem.

`exists_section_forInverseCoefficient` assumes full standard type of the
blocks and a nonzero inverse functional `J` on their actual lower induction.
The preceding lower-type theorem gives full inverse type of that induction.
Its functional space is a line, so every supplied inverse functional `ell'`
is `c • J` for some complex scalar `c`. Every coefficient `Z` in the actual
model of `ell'` is `modelMap ell' v` for a section `v`, by intrinsic modelMap
surjectivity. The section `c • v` has coefficient `Z` for `J`, by linearity.
No nonzero hypothesis on `ell'` or `Z` is used; when `c=0` the same argument
still applies. All fields and dependent block-carrier universes are retained.

`sectionForInverseCoefficient` chooses such a section and its specification
records equality in the actual Whittaker-function space.
`jacquetFunction_sectionForInverseCoefficient` assumes that the coefficients
of `J` realize the ordinary Jacquet integrals. Evaluating the specification
at each ambient element then identifies the chosen section's Jacquet function
with the originally supplied coefficient. The unfolded-series theorem uses
the preceding actual radical-average series identity and this coefficient
equality, retaining the supplied additive Haar rectangle measure and arbitrary
Borel quotient measure. It requires no test-model, smoothness or convergence
hypothesis for that total-integral equality.

`exists_uniformJacquetCoefficientRealization` applies the published ordinary
Jacquet functional theorem for full-type blocks, supplied nonzero inverse
block functionals and the supplied self-dual additive Haar measure. Its one
real bound precedes the deformation parameter; for every parameter above
that bound, all raw Jacquet integrands are absolutely integrable and a nonzero
functional J realizes them. After that J is chosen, every induced inverse
functional and every coefficient in its actual model is realized by one
section, at all ambient group elements simultaneously. The proof transfers
full type to the two opposite twists and applies the chosen-section theorem.
The bound is independent of the supplied induced functional and coefficient.
It is not a uniform support bound, a holomorphic choice of sections or a
parameter-continuation assertion. Zero induced functionals and coefficients
are included; the nonzero hypotheses concern only the block functionals
needed by the ordinary existence theorem and the reference functional J.
