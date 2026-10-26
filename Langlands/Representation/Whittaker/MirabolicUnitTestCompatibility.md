# Compatibility of compact mirabolic test data

Author: Worker 408.

This internal helper relates concrete mirabolic test data to the published
`Langlands.Whittaker.IsMirabolicTestFunction` predicate and the quotient
indicator used by the equal-rank assembly step. It proves two conditional
lemmas about specified functions and names their actual quotient support set.
Construction of those functions, Kirillov
lifting, the last-row test, and the unit-value theorem remain separate
obligations.

## Parameters and existing objects

Both lemmas work over any field `F : Type uF` with a topology and every
`n : ℕ`. They use the actual `GeneralLinear (n + 1) F`, its published
mirabolic subgroup and upper-unipotent subgroup, the existing standard and
inverse equivariant-function subtypes, and the existing left quotient.
There is no local-field, topological-ring, separation or measure assumption.
The case `n = 0` is included. A supplied p-adic topology can be installed
before using these lemmas.

Write `P` for the actual mirabolic subgroup, `N` for the actual
upper-unipotent subgroup, and `K : Subgroup P`. Let
`C = (fun k : P => k.val) '' (K : Set P)` and
`S = {g | ∃ u : N, ∃ k : K, g = u.val * k.val.val}`.
These are abbreviations in this explanation. The definition
`mirabolicQuotientSupport K` is exactly `q(C)`, where `q` is the existing
left-unipotent quotient map. It introduces no alternative subgroup, quotient
or function space. The definition applies to every `K` and asserts neither
compactness nor openness.

## The shared test-function predicate

`isMirabolicTestFunction_of_compact_mirabolic_support` takes a standard
equivariant function `φ`, compactness of `K`, and an ambient open subgroup
`J` whose intersection with `P` is contained in `C`. It assumes that `φ`
vanishes outside `S` and is right invariant under every element of `K`,
at every ambient matrix. Its conclusion is precisely the existing
`IsMirabolicTestFunction ψ n φ`.

For its smoothness clause, an element of `J` that is mirabolic has a
representative in `K` by the assumed containment. The given right invariance
then proves the required equality for right multiplication on mirabolic
matrices. For its support clause, `C` is compact by continuity of subgroup
inclusion. A nonzero value forces membership in `S`, which supplies exactly
the unipotent element and compact representative required by the predicate.
The proof uses the specified `J` and the image of the specified `K`.
It needs neither openness of `K` nor compactness of `J`.

## Product on the actual quotient

`mirabolicTests_product_eq_quotient_indicator` takes opposite-character
functions `φ` and `φ'`. On every product `u k` it assumes their values
are respectively `standardCharacter ψ n u` and its complex inverse.
Outside `S` both functions vanish. The conclusion says that their product
at every ambient matrix `g` is the complex indicator of
`mirabolicQuotientSupport K = q(C)` at `q(g)`,
where `q` is the published left-unipotent quotient map.
This lemma imposes no compactness or invariance condition on `K`.

If `q(g)` belongs to `q(C)`, choose `k ∈ K` with `q(k) = q(g)`.
The quotient's existing right relation gives `g * k⁻¹ ∈ N`, so
`g = u k`. The two prescribed values multiply to one because character
values are units. If `q(g)` lies outside `q(C)`, a factorization `g = u k`
would give equality of those quotient classes. Hence `g` is outside `S`,
and the zero-extension clause makes the product zero.

## Provenance and consumer scope

This is internal content derived directly from `ModelKirillovStatement`,
`Group.GL.Mirabolic` and the actual quotient map and relation imported through
`Analysis.Local.QuotientTopology`. The proofs use continuous subgroup
inclusion, nonzero values versus zero extension, the existing quotient
equality criterion, and cancellation of a nonzero complex character value.
No representation-theoretic theorem from the literature is invoked.

The conditions match the concrete data requested by
`MirabolicUnitTestStatement`: its open mirabolic subgroup can be passed
through `toSubgroup`, and its ambient subgroup and support clauses supply
the first lemma's hypotheses. For the inverse function, the first lemma
applies after expressing that function as a standard-equivariant function
for the inverse additive character. The product lemma directly accepts
the existing inverse-function subtype. Restricting its conclusion to
mirabolic matrices supplies the first condition of
`RankinSelberg.IsEqualRankCompactTest` when the coefficient functions
agree there with these tests. The actual test construction and that
coefficient agreement are inputs to future work.
