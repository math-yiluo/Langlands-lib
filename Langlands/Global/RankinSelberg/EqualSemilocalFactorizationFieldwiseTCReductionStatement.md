# The equal-rank semi-local factorization premise from totally complex data

Module `Langlands.Global.RankinSelberg.EqualSemilocalFactorizationFieldwiseTCReductionStatement`,
namespace `Langlands.Global.RankinSelbergGlobal`. The proposition has independent universes
`u` for number fields and `uQ` for the spectral presentations.

## Statement

`EqualSemilocalFactorizationFieldwiseTCReductionStatement` has two premises:

1. `ComplexEqualFunctionalEquationStatement` from
   [`ArchimedeanFunctionalEquationStatement`](ArchimedeanFunctionalEquationStatement.md):
   the equal-rank local functional equation at each complex place, with its integral and
   continuation data. Its field quantifier is unchanged: it concerns complex places of
   arbitrary number fields with the hypotheses of that statement.
2. `EqualArchimedeanFactorizationTCStatement` from
   [`EqualFactorizationAtStatement`](EqualFactorizationAtStatement.md): integrated
   equal-rank factorization at each totally complex number field `F`, given by
   `EqualArchimedeanFactorizationAt F`. This retains the two Schwartz–Bruhat and
   Fourier row-function product formulas, the ordinary and dual integral product
   identities with the same nonzero constant, and the nonvanishing clauses. No integrated
   factorization at a field with a real place is assumed.

The conclusion is the unchanged `EqualSemilocalFactorizationTCStatement` from
[`EqualSemilocalReductionTC`](EqualSemilocalReductionTC.md). For the local and global data
of that proposition at a totally complex `F`, it gives suitable cuspidal vectors,
Schwartz–Bruhat data, a common right half-plane and two meromorphic archimedean factors.
Those factors are nonzero off discrete sets, obey the archimedean functional equation
with a sign, and multiply the finite test integrals at `S` to give the ordinary and dual
partial integrals. The conclusion also retains the nonvanishing of the finite test
integrals in each right half-plane and the relation of the sign to the finite central
scalars whenever those scalars satisfy `HasMinusOneScalar` on the tests. The real-place
families still occur but their index subtype is empty at `F`.

## Provenance and proof boundary

The existing theorem `equalSemilocalFactorizationReductionTC` in
[`EqualSemilocalFactorizationReductionTC`](EqualSemilocalFactorizationReductionTC.md)
assumes integrated factorization over all number fields, but applies it only at the field
`F` of the conclusion. The intended proof adapts that argument to use the second premise
at this `F`. The same empty-real-place argument supplies the real local clauses. The
central-sign input is available as `archimedeanCentralSign` in
[`ArchimedeanCentralSignProof`](ArchimedeanCentralSignProof.md), so it is not a third
premise of the new target. This is a refinement of the Library's assumption, not a new
form of the local equation or a change to any unrestricted target (including
`EqualSemilocalFactorizationStatement`).

This module states the implication only. It does not establish either premise, the
implication itself, or a functional equation. Once the implication is proved, the
existing `equalSemilocalReductionTC` consumes its conclusion to obtain
`EqualSemilocalEquationTCStatement` with the same two premises. This does not require
an unequal-rank equation.

**Source.** J. W. Cogdell, *Analytic theory of L-functions for GL_n*, in J. Bernstein
and S. Gelbart (eds.), *An Introduction to the Langlands Program*, Birkhäuser, 2004,
pp. 197–228, `cogdell-2004-analytic-theory-gln`, proof of Theorem 4.1, printed pp. 219–220
(PDF pp. 222–223), the equal-rank product with a Schwartz function and the combination
of the ordinary and dual products with the local equations and signs (described as
analogous for equal ranks on p. 220). The restriction to totally complex fields and the
exact Lean division into premises are derived interfaces.
