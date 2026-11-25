# The unequal-rank semi-local equation from factorization over totally complex fields

Module `Langlands.Global.RankinSelberg.UnequalSemilocalFieldwiseTCReductionStatement`,
namespace `Langlands.Global.RankinSelbergGlobal`. The only declaration is a `Prop`-valued
statement, at independent universes `u` (number fields) and `uQ` (spectral presentations).

## Statement

`UnequalSemilocalFieldwiseTCReductionStatement` says that the following two premises
imply `UnequalSemilocalEquationTCStatement`:

1. `ComplexUnequalFunctionalEquationStatement` from
   [`ArchimedeanFunctionalEquationStatement`](ArchimedeanFunctionalEquationStatement.md):
   the unequal-rank local functional equation, including the integral and continuation
   data in that statement, at every complex place of a number field. This premise still
   ranges over number fields with the original hypotheses; it is about complex places
   only, even for a field that also has real places.
2. `UnequalArchimedeanFactorizationTCStatement` from
   [`UnequalFactorizationAtStatement`](UnequalFactorizationAtStatement.md): the integrated
   factorization and nonvanishing clauses at each totally complex number field `F`, as
   `UnequalArchimedeanFactorizationAt F`. Factorization at a field with a real place is
   not a premise.

The conclusion is the existing proposition in
[`SemilocalEquationTCStatements`](SemilocalEquationTCStatements.md), unchanged. For the
specified actual cuspidal data and local parameters over totally complex `F`, it gives
spherical-outside-`S` vectors and meromorphic continuations of the ordinary and dual
partial integrals that are nonzero off discrete sets. Its equation relates those
continuations with the archimedean factors and the product of the p-adic gamma factors
at `S`, off a discrete set, with the additive characters, measures and normalization of
the existing statement. There is no equal-rank input and no real-place functional
equation input. The real-place families already in the conclusion are still present,
indexed by the empty subtype of real places at `F`.

## Provenance and proof boundary

This is an internal refinement of the totally complex route in
[`UnequalSemilocalArchimedeanReduction`](UnequalSemilocalArchimedeanReduction.md),
toward the unequal-rank semi-local functional equation. In that module
`UnequalSemilocalArchimedeanReduction.factorization_at` applies its integrated
factorization hypothesis only at its field argument `F`; the original hypothesis
nevertheless quantifies over all number fields. The intended proof reuses that argument
with `UnequalArchimedeanFactorizationAt F` as the input at `F`, which the second premise
supplies because `F` is totally complex. The empty real-place subtype gives the vacuous
real-place equation input at this step, just as in the existing
`UnequalSemilocalArchimedeanReduction.unequalSemilocalFactorizationTC_of_parts`.
The central sign is not a separate premise: `archimedeanCentralSign` in
`ArchimedeanCentralSignProof` proves it for the original scope. Once the same-field
step supplies `UnequalSemilocalFactorizationTCStatement` (declared in the module of
that name), the intended final step is
`unequalSemilocalEquationTC_of_factorizationTC` from `UnequalSemilocalEquationTCReduction`.

No proof of the statement is included. In particular the old reduction cannot simply
be given a factorization hypothesis restricted to totally complex fields in place of its
unrestricted one. The unrestricted entry points are unchanged. The two premises
here, and the equal-rank and global steps of the chain, are not proved by this statement.

**Source.** J. W. Cogdell, *Analytic theory of L-functions for GL_n*, in J. Bernstein and
S. Gelbart (eds.), *An Introduction to the Langlands Program*, Birkhäuser, 2004,
pp. 197–228, `cogdell-2004-analytic-theory-gln`, proof of Theorem 4.1, printed pp. 219–220
(PDF pp. 222–223), the unequal-rank product expressions and combination of the local
functional equations and signs. The quantifier restriction and the separation of local
and integrated inputs are derived from the Library's reduction, not an independently
named source theorem.
