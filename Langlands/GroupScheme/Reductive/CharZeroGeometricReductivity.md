# Characteristic-zero invariant separation for reductive groups

This derived construction applies the proved characteristic-zero
complete-reducibility theorem to the existing invariant-linear-form construction.
It works over every algebraically closed field `k : Type u` of characteristic
zero, with arbitrary `u`, for the unchanged `IsPseudoReductive G`,
`MatrixRepresentation G n` and `IsFixedVector` predicates. The finite coordinate
type `n` lies in `Type`, as in `ReductiveGeometricReductivityStatement`.

`MatrixRepresentation.exists_normalized_invariant_polynomial_of_reductive_charZero`
produces a homogeneous polynomial of degree one taking value one at the supplied
nonzero fixed vector. The proof obtains smoothness from `hG`, invokes
`reductiveCharZeroSemisimplicityStatement` for the actual rational-point
representation, and applies
`MatrixRepresentation.exists_dual_fixed_of_rational_semisimple`. This gives
coefficients `c` fixed by the dual representation with `c` paired against the
given vector equal to one. The polynomial is `linearPolynomial c`. Its previously
proved evaluation formula gives the normalization, and the dual pairing identity
gives invariance over every test scheme.

`MatrixRepresentation.charZeroInvariantPolynomial` chooses such a polynomial
using classical choice. `charZeroInvariantPolynomial_spec` records all three
properties together: degree-one homogeneity, invariance for every scheme
`T` over `Spec k`, every `g : T ⟶ G.X` and every section-valued coordinate
vector, and evaluation equal to one at the given fixed vector. The tests may be
nonaffine or nonreduced. This is an existence-based construction; no algorithm for
computing its coefficients is claimed.

`invariant_polynomial_of_reductive_charZero` gives exactly the polynomial
conclusion of `ReductiveGeometricReductivityStatement` under the additional
characteristic-zero hypothesis. It applies the existing conditional consumer
`invariant_polynomial_of_reductive_charZero_semisimplicity` to the proved theorem
`reductiveCharZeroSemisimplicityStatement`. That consumer chooses degree one.
Complete reducibility is thus discharged by the imported proof, with no
semisimplicity or linear-reductivity premise in this new theorem. The
positive-characteristic part of Haboush's theorem remains outside this unit.

Provenance: Mumford, Fogarty and Kirwan, *Geometric Invariant Theory*, third
enlarged edition (1994), Appendix to Chapter 1, Section A, printed p.191 (PDF
zero-based page index 202), definitions (ii) and (iii), the implication from linear
to geometric reductivity, and the characteristic-zero equivalence of reductivity
and linear reductivity. Registered source:
`mumford-fogarty-kirwan-1994-git-3rd`. The normalized chosen polynomial is the
coordinate construction derived from the Library modules
`Reductive.InvariantLinearForm` and `Reductive.CharZeroSemisimplicityProof`.
The latter implements the Lie-algebra route to complete reducibility; its proof
and supporting module explanations supply that prerequisite.
