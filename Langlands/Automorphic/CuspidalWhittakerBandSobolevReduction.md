# Actual multiplicity one from compact Sobolev bounds and analytic comparison

`CuspidalWhittakerBandSobolevReductionStatement.{u}` retains exactly two named
open premises, `OperatorCompactSobolevStatement.{u}` and
`CuspidalWhittakerBandSobolevComparisonStatement.{u}`, and has the exact existing
`CuspidalOperatorMultiplicityOneStatement.{u}` as its consequent. The number
field universe remains arbitrary and free, and the rank parameter includes
r = 0. The unconditional multiplicity-one task remains open.

The first premise is the fixed-finite-level compact pointwise Sobolev estimate
on actual operator realizations with unitary central character, using genuine
enveloping derivatives and the actual determinant-band quotient Haar L² norm.
It is the separately owned statement motivated by Shalika (1974), Lemmas 5.6
and 5.7, printed pp.187–188. Its proof, including comparison with the
center-quotient norm in the original source, remains required.

The second premise applies only to actual cuspidal operator realizations with
unitary central characters. It takes a full operator equivalence, a standard
global additive character, actual determinant-band integrability witnesses,
and the two `CuspidalWhittakerBandBound` predicates. Its conclusion is one
complex scalar comparing the actual Whittaker coefficients along the supplied
equivalence, uniformly over all original vectors and group points. This
analytic comparison is explicitly assumed, not proved by the module.

The implemented proof applies the published `cuspidalWhittakerBandReduction`
and supplies its band-bound premise using
`cuspWhittakerBandBound_of_compactSobolev` from
`CuspidalWhittakerBandSobolevEstimate`. That helper obtains a uniform compact
evaluation set from compact domination, applies the supplied Sobolev estimate
on that set, and transfers the bound to the actual Whittaker coefficient.

The imported band reduction handles unitary-central-character normalization
by a common actual Hecke determinant twist, chooses the standard global
additive character, and obtains actual L² integrability from the published
cuspidal band-cover theorem. The retained comparison premise then gives a
scalar comparison, and actual Whittaker reconstruction gives equality of the
operator realizations. No extra premise appears in the consequent.

This is an internal derived reduction authorized by Task 7293 revision 1.
The source motivation is Shalika, *The multiplicity one theorem for GL_n*
(1974), Theorem 5.5 and Lemmas 5.6–5.9, printed pp.187–189. Shalika works with
unitary adelic group representations in a cuspidal Hilbert space; the Library
starts from actual finite, compact, and infinitesimal operator realizations.
The formal reduction does not silently identify these settings.

In particular, the retained comparison premise still contains substantive
open work: compatible full-group Hilbert globalizations, extension of the
supplied full operator equivalence, comparison of actual enveloping derivative
seminorms with smooth Hilbert derivative seminorms, and continuous local and
all-place Whittaker uniqueness. A generic invariant positive form, or
algebraic Harish-Chandra module uniqueness without continuity, does not
discharge this premise. The finite-level bounds alone are not asserted to
establish uniqueness.
