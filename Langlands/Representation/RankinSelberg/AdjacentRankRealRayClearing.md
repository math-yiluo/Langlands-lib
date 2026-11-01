# Actual corank denominator bounds and formal clearing

This internal composition applies Worker 1191's
`TwoBlockFirstBlockLaurent.cleared_series_eq_of_spectral_uniqueness` to the
literal determinant-slice coefficient series of a corank-one integral.
Scalar spectral uniqueness remains explicit.

`corankOneCoefficient_denominatorBound_clearing` takes full Whittaker type
for the two representations, specified nonzero standard and inverse-character
functionals, and vectors in their actual coefficient images. It preserves the
canonical field structures, the supplied compatible quotient measure, the
additive Haar measure, and independent carrier universes. It permits reducible
representations and does not require self-duality.

The published zero-row unequal-rank analytic theorem supplies an actual rational
continuation. The zero-row integral identity makes it a continuation of the
corank integral. The supplied reciprocal Laurent-span bound and nonzero
polynomial yield a finite Laurent lift of the product of that polynomial and
this rational continuation. The published full-type corank convergence theorem
and actual determinant-slice expansion supply both weighted absolute
summability and the correct `HasSum` on a right half-plane. Worker 1191's bridge
then gives the formal coefficient identity. The algebraic cancellation takes
place only in the field of rational functions; no polynomial is cancelled on
the bilateral coefficient module.

The unchanged bridge pair is reused from Worker 1191's reviewed draft and is
credited to him. This module proves neither the scalar spectral uniqueness
proposition nor either exact adjacent-rank parent proposition.

`SecondBlockCorankRealRayDenominatorBound` records the rational reciprocal
bound on a real ray for the same actual family, functionals and vectors as
`SecondBlockCorankRealRayClearing`. Its polynomial is exactly the fixed
polynomial times the spectral rescaling of the second polynomial.

`secondBlockDeformed_isOfWhittakerType` derives full standard type at every
complex parameter. Each determinant-power twist has open kernel and is
trivial on the upper unipotent subgroup, so it preserves full block type.
The published complete reversal and normalized-induction theorem supplies
full inverse type for lower induction; the standard/inverse equivalence
then supplies full standard type. No induced-type premise is added.

`secondBlock_realRayClearing_of_denominatorBound` applies the actual corank
clearing theorem to every parameter, nonzero functional and vector. Constant
coefficient one for the two fixed polynomials ensures that their rescaled
product is nonzero. Thus rational real-ray denominator bounds imply formal
real-ray clearing; the supplied scalar spectral uniqueness hypothesis remains
explicit. Constructing those rational bounds from fixed block certificates
remains a separate obligation.

The canonical local instances have module-specific names with prefix
`realRayClearing`, so this module can be imported together with
`AdjacentRankClearedContinuation`. This naming correction changes no
mathematical declaration or proof route.
