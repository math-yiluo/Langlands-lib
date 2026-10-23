# Finite dual exponents and tempered class exponents

Author: Worker 19.

This family states the finite dual-spectrum and class-exponent prerequisites
for the weakly critical refinement of tempered support. These are proposition
definitions, not proofs.

## Actual objects and normalization

The field is an actual `PadicField p` in universe `uF`, equipped with
`TopologicalData T`. The rank is positive and `B` is any standard block shape.
The ambient representation is `A : Rep.{uV} ℂ (GeneralLinear n F.Carrier)`.
`IsAdmissible` includes smoothness; irreducibility is a separate hypothesis.
The full-dual spaces and nilpotence index are those constructed in
`Exponents.DualJacquet`.

`T.IsOppositeJacquetClassExponent B A S` means that `S` is irreducible and
admissible and is a quotient of an actual invariant subspace of
`CuspidalJacquetMultiplicity.oppositeJacquet T B A`. It supplies no occurrence,
filtration, quotient or classification as object data. This is the Jacquet
realization of a class exponent: the source's Lemma 3.2.2(2) and Theorem 3.2.4
identify class exponents with these irreducible subquotients. The definition
uses representatives of isomorphism classes, and its constituent universe
`uW` is independent of `uV` and `uF`. No matrix-coefficient asymptotic module is
constructed here.

The opposite quotient is by the actual lower block unipotent subgroup. Its
normalization uses the inverse of the upper full modulus; hence the upper
positive half-modulus multiplies the source action. The dual action is
transposition on the full algebraic dual restricted to block scalars, with
no inversion or complex conjugation. `IsDualJacquetExponent` requires an open
character kernel and a nonzero exponent-one space. Its nilpotence index is
the least uniform order on the entire generalized component, valued in `ℕ∞`.

The existing `Classification.HasScalarCharacter` expresses
`S.ρ (B.blockScalarLevi a) v = χ(a) • v` for all block scalars `a` and vectors
`v`. This is scalar action, not generalized scalar action. For a product of
positive-rank general linear groups, block scalars are exactly the center.
The statement does not use a chosen central character as a field of a class.

## Four statements

`GLDualJacquetFinitenessStatement` assumes `A` irreducible and admissible and
asserts that its set of smooth dual exponents is finite, each occurring
generalized component has nilpotence index less than infinity, and the supremum
of those actual generalized subrepresentations is the full dual space. The
last clause asserts spanning; it does not separately assert independence of
the components or a chosen direct-sum equivalence. These are consequences
stated in the source's direct-sum discussion on p.91. No finite dimensionality
of the full dual or of the generalized components is claimed.

`GLDualJacquetClassExponentStatement` has the same source hypotheses. For
every character `χ`, it equates dual-exponent occurrence with existence of an
irreducible admissible opposite Jacquet constituent with scalar split-center
character `χ`. The existential representative has carrier in `uV`, the
universe of the original representation and its quotient and subquotients.
This does not force its carrier to be the original vector space. The result
combines the dual/exponent equality of Corollary 3.2.5(1), the realization by
opposite Jacquet constituents in Lemma 3.2.2(2) and Theorem 3.2.4, and the
central-exponent occurrence in Lemma 3.2.1 and its converse.

`GLTemperedJacquetClassExponentStatement` assumes the source irreducible and
analytically tempered, and takes an actual irreducible admissible opposite
Jacquet constituent `S` in independent universe `uW` with prescribed scalar
split-center character `χ`. For any Borel Haar measure on the actual quotient
of the Levi by its full center, it states that `S` is analytically tempered
modulo that center if and only if `χ` has norm one everywhere. This is
Lemma 4.5.6 after Corollary 3.2.5(1): a weak exponent is a unitary exponent,
and a weak class exponent is a tempered class exponent. Analytic temperedness
and norm-one character occurrence are distinct predicates connected by this
statement, not identified by definition.

`GLUnitaryDualJacquetTemperedSupportStatement` retains a prescribed unitary
dual exponent `χ` of an irreducible tempered `A`. It asserts existence of an
irreducible admissible opposite Jacquet constituent `S` with scalar character
`χ`, analytically tempered for every Borel Haar measure on the full central
quotient, and an injective intertwiner from `A` to normalized opposite
parabolic induction of `S`. This is Corollary 4.5.7, including the prescribed
central exponent. The constituent clause is the source
assertion that the inducing class is a weak class exponent, realized through
the actual opposite Jacquet quotient. This
support representation need not be discrete series.

`GLDualJacquetExponentPrerequisitesStatement` is the conjunction of these four
declarations. It retains independent field, source and arbitrary-constituent
universes. No existence of a quotient, decomposition or intertwiner is assumed
as a premise.

## Original sources, derived translation and limits

The original is A. J. Silberger, *Introduction to harmonic analysis on reductive
p-adic groups* (1979), registered as `silberger-1979-harmonic-analysis`, retained
SHA-256 `b9432812bb48ce0bcd3975144baa6b3cca99bcaaf0d33d785ce68e94e02854fc`.
The relevant printed pages are pp.90–92 (PDF pp.96–98), pp.120–123
(PDF pp.126–129), and pp.187–188 (PDF pp.193–194). The formulas are checked in
the original page images.

This is a derived specialization to standard block parabolics of `GL_n`.
It expresses the source's class-exponent comparison using actual normalized
opposite Jacquet subquotients and its weak-exponent comparison using the
Library's analytic `L^(2+ε)` temperedness. Equivalence of that analytic
criterion with the source's tempered coefficient space is part of the
mathematical content of the comparison, using the tempered criteria developed
in Chapter 4. It is not an assumption equating arbitrary predicates.
The source's finite integer `d(χ)` is expressed by finiteness of the already
constructed least uniform `ℕ∞` index, with the same normalization and order.

No coefficient asymptotic expansion, equality of asymptotic multiplicities,
weakly critical support statement, arbitrary-reductive-group realization, or
proof of the four statements is supplied. The analytic Haar interpretation
of the explicit block modulus remains an upstream obligation. These
statements prepare the strict nilpotence comparison on proper refinements;
they do not assert that comparison or a discrete-series refinement themselves.
