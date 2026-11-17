# Finite equal-rank data nonvanishing on every right half-plane

This internal module proves
`Langlands.Global.RankinSelbergGlobal.EqualNonvanishing.PadicEqualNonvanishingTestStatement`
for every p-adic field, using the already proved local unit-value and normalized
functional-equation theorems. Its proof is `padicEqualNonvanishingTest`. This
supplies a finite local test-choice ingredient for the equal-rank global target;
it does not prove the global factorization theorem.

The result is derived implementation infrastructure. It uses the published
`Langlands.RankinSelberg.equalRankUnitValue` and
`Langlands.RankinSelberg.equalRankFunctionalEquation` and elementary consequences
of their rational-continuation statements. It claims no new direct translation
of an original source.

## Exact scope

Fix `K : PadicField p`, its canonical topology and Borel measurable spaces, a
unitary nontrivial additive character `ψ`, and a supplied additive Haar measure
`ν` self-dual for `ψ`. Let `π` and `σ` be representations of `GL_(r+1)(K)` on
complex vector spaces in independent universes. Assume the published
`IsOfWhittakerType` predicates for `π` with the standard character of `ψ` and for
`σ` with its inverse standard character. Fix respective nonzero Whittaker
functionals `ℓ`, `ℓ'`.

Then there is actual `EqualLocalTestData K ψ ν π σ`, denoted `D`, such that:

- `D.ℓ = ℓ` and `D.ℓ' = ℓ'`;
- the actual integral `D.integral` has rational continuation equal to one;
- for every real `a` there is a complex `s` with `a < s.re` and `D.integral s ≠ 0`;
- for every real `a` there is a complex `s` with `a < s.re` and `D.dualIntegral s ≠ 0`.

The last two clauses have separate existential quantifiers. The statement uses
exactly the existing normalized quotient Haar measure in `EqualLocalTestData`.
Its Fourier partner belongs to the actual local Schwartz–Bruhat space and
satisfies the existing `IsRowFourierPair` relation for `ψ`, `ν`. Rank `r = 0`
means `GL_1` and is included. The field and both representation-carrier universes
remain independent. There is no additional open theorem premise beyond the
specified local mathematical hypotheses.

The statement does not assert that arbitrary preselected model vectors or tests
have these nonvanishing properties. It chooses their coefficient vectors and
test function while preserving the supplied Whittaker functionals.

## Implemented proof

`nonvanishing_on_right_of_rational` starts with any nonzero rational
continuation of a function on `ℂ`. Its numerator is a nonzero polynomial. For
`q > 1`, only finitely many real parameters have a spectral point `q^(-s)` at a
root of that numerator, by `finite_spectralPoint_roots`. Given a desired lower
bound, choose a real parameter larger than it and the continuation threshold,
outside this finite set. The continuation denominator is nonzero there by its
definition, so the actual function value is nonzero. This proves nonvanishing
arbitrarily far right, without extending the asserted equality to poles.

`dual_ne_zero_of_normalized` applies to the published normalized functional
equation when its ordinary rational continuation and ordinary normalization
polynomial are nonzero. If the dual rational continuation were zero, choose a
real parameter avoiding the finite root sets of the ordinary numerator,
ordinary denominator and ordinary normalization polynomial. The equation has
left side zero and right side nonzero: its other factors are powers of units
and the nonzero epsilon monomial. This contradiction proves that the dual
continuation is nonzero. No assumption on a value at a pole enters the argument.

For `padicEqualNonvanishingTest`, the proved `equalRankUnitValue` theorem gives
coefficient vectors `f`, `f'` and a test `Φ` whose actual ordinary integral has
rational continuation one. The proved `equalRankFunctionalEquation` theorem,
applied with the normalized quotient Haar measure and the supplied self-dual
`ν`, gives a Fourier partner `Φhat`, ordinary and dual continuations, and their
normalized functional equation. Uniqueness of rational continuation identifies
the ordinary continuation with one. The ordinary normalization polynomial is
nonzero by its normalized-generator property, so
`dual_ne_zero_of_normalized` proves the dual continuation nonzero. The two
applications of `nonvanishing_on_right_of_rational` give the required
nonvanishing clauses. The witnesses are bundled into `EqualLocalTestData` with
the original `ℓ`, `ℓ'`.

## Remaining global obligations

This local existence theorem does not realize these prescribed coefficient
vectors as factors of a single global Whittaker function, choose archimedean
tests with nonvanishing local products, or compare global and local quotient
measures. Those obligations in `EqualPointwiseFactorizationStatement` and the
unconditional proof of `ArchimedeanFactorizationStatement` remain open.
