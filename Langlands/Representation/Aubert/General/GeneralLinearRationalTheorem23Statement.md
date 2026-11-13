# Actual rational-point GL target for Aubert Theorem 2.3

The namespace is `Langlands.Aubert.General.RationalPointFamily.GL`. This module
contains seven Prop-valued definitions and no theorem. Its entry target is
`RationalTheorem23Statement.{u, v}`. It is a derived transport target for the
actual rational-point objects of `GeneralLinearRationalGraded`, using the
existing matrix statements and proofs named below.

## Source and scope

The source motivation is Aubert 1995, *Dualité dans le groupe de Grothendieck
des représentations lisses de longueur finie*, printed pp. 2184–2185:
Définition 2.1, Remarque 2.2 and Théorème 2.3. The registered source is
`aubert-1995-duality`, SHA-256
`57af9c46769f6edd8e142ddaf465e89acfa2f2147db222d26879a28a06df9693`.
The unadjusted operator is Définition 1.5, printed p. 2181. This module
specializes those comparisons to the existing p-adic GL development and
expresses them on actual rational-point exact K0; it makes no new translation
of a general reductive-group theorem.

Fix `F : PadicField.{u} p`, `[Fact p.Prime]` and
`T : F.TopologicalData`. Representations are smooth complex representations
with carrier universe `max (u + 1) v`, where `u` and `v` are independent.
`RationalGeneralLinear F N` is the group of actual rational points of the
group scheme `GL_(Fin N)`, with `rationalGLTopology F T N`, its evaluation
topology from `T`. All natural ranks, including zero, occur.
`RationalGLK0` is the exact finite-length Grothendieck group with all actual
short-exact-sequence relations, including nonsplit sequences.
The graded group is its direct sum over all ranks.

The field scope here follows the existing matrix GL modules. The general
reductive program's arbitrary nonarchimedean local fields remain a separate
requirement. The target retains three matrix-side representation-theoretic
premises for the whole ring:

| Premise | Meaning |
| --- | --- |
| `hx : Aubert.BinaryProductExactnessStatement F T` | The actual normalized binary induction product preserves finite-length short exact sequences in each variable. |
| `hl : Aubert.GradedInductionRingLawsStatement F T hx` | Associativity, commutativity and the two unit laws for the resulting matrix multiplication. |
| `hp : Aubert.SegmentPolynomialComparisonStatement F T hx hl` | Bijectivity of polynomial evaluation on the actual segment classes in the whole graded induction ring. |

These premises are at universes `u, max (u + 1) v`. The definitions of the
other component targets have no `hx`, `hl` or `hp` parameter. In the final
conjunction they are asserted for each supplied triple, together with the
whole-ring result. This conditional target does not discharge the three
premises or establish completion of the parent program.

## The component targets

`RationalUnadjustedOperatorIdentificationStatement` preserves the full setup
of the published `RationalAlternatingOperatorComparisonStatement`.
For every rank and every strictly decreasing cocharacter of the diagonal
torus it asserts local compactness, nonarchimedeanity and the Hausdorff
property of the actual rational-point group. For arbitrary instances of
those properties, it then asserts the existence of closed unipotent groups,
closed parabolics, continuous Levi projections, the limit-of-compact-subgroups
property of each unipotent group, and finite-length preservation of normalized
induction and Jacquet restriction. Finally, for every such set of premise
proofs it asserts equality of linear operators:

`rationalUnadjustedOperator F T N = rationalAlternatingOperator ...`.

The right side is the literal actual rational-point standard-family sum,
using `standardCocharacter`, the diagonal torus's relative root system,
normalized positive induction half-modulus and inverse Jacquet half-modulus.
The left side was defined by exact-K0 conjugation of the current matrix
operator. Thus the conclusion identifies that transport with the literal
standard-family construction. The separate existential clause ensures the
comparison hypotheses are supplied, and universal quantification over their
witnesses retains the existing statement's proof-independence scope.

`RationalSupportAdjustmentStatement F T` has two clauses, for every rank.
For an actual irreducible rational-point module `E`, let `x` be its exact
class, with finite length obtained from irreducibility. Then

`rationalAdjustedOperator F T N x =
  rationalSupportSign F T N E hE • rationalUnadjustedOperator F T N x`.

For every block shape `B`, irreducible Levi module `σ` which is
quasicuspidal, and support presentation exhibiting the inverse pullback of
`E` as a subquotient of the actual normalized induction of `σ`, the same sign
is `(-1 : ℤ) ^ (N - B.length)`. The pullback uses the inverse of
`rationalPointsContinuousMulEquiv N F.Carrier`. This is precisely the
inherited matrix support convention, applied to the actual module.
The intended reuse is `Aubert.adjustedOperator_irreducible` and
`Aubert.supportSign_of_support`.

`RationalRankZeroStatement F T` asserts that both complete rank-zero
operators are the identity linear map and that the support sign of each
actual rank-zero irreducible is one. It retains the matrix convention given
by `Aubert.alternatingOperator_rankZero`, `Aubert.adjustedOperator_rankZero`
and `Aubert.supportSign_rankZero`.

`RationalGradedHomogeneousStatement F T` asserts that the whole graded
adjusted operator restricts on every homogeneous inclusion to the rankwise
adjusted operator. It is the rational-point form of
`Aubert.gradedOperator_homogeneous`.

`RationalSegmentSocleHeadStatement F T` quantifies over every existing
`T.Segment` and every supplied strong segment socle `πZ` and special quotient
`πS`. Their irreducibility supplies finite length. Pull both actual modules
to rational points along the canonical continuous group equivalence and
denote their exact classes by `x` and `y`. The conclusion is

`rationalUnadjustedOperator F T Δ.degree x =
  (-1 : ℤ) ^ (Δ.degree - Δ.length) • y`.

This is the full signed class formula for the actual modules, using the
existing `Aubert.segmentSocleHead`; it does not claim an isomorphism from an
arbitrary equality of Grothendieck classes.

`RationalWholeGradedTheorem23Statement F T hx hl hp` installs the existing
matrix induction ring and its transported rational-point induction ring.
It asserts all seven of the following:

1. The adjusted rational-point operator preserves multiplication on every
   pair of elements of the whole graded ring.
2. It preserves the unit, the class transported from the trivial line in
   rank zero.
3. It is involutive on the whole graded additive group.
4. The transported Zelevinsky ring endomorphism is involutive.
5. These two operators agree as integer-linear maps.
6. The polynomial equivalence evaluates every polynomial by matrix segment
   evaluation followed by the canonical graded pullback equivalence.
7. For every finite multiplicity function on segments, the rational-point
   monomial basis vector is the actual matrix segment-monomial class
   transported by that equivalence.

The last two formulas concern the complete polynomial ring and the complete
additive basis, including the empty monomial. Their intended reuse is the
existing `Aubert.segmentPolynomialEquiv`, `Aubert.segmentMonomialBasis` and
their definitions; the whole-operator assertions use the published
`Aubert.aubertTheorem23`, `Aubert.adjustedInvolutivity` and the unit formula.
No assertion here replaces the whole polynomial comparison `hp` by a
calculation only on segment generators.

`RationalTheorem23Statement` is the conjunction of the unadjusted
identification target and, for every field, topological data and
`hx`, `hl`, `hp`, the support adjustment, rank-zero, homogeneous, segment and
whole-graded targets, in that order. All component formulas use the same
canonical exact-K0 pullback and its inverse.

## Provenance, corrections and remaining proof

This is an internal reformulation of the published matrix results using
`FiniteLengthGrothendieckGroup.pullbackEquiv` and
`GroupScheme.GeneralLinear.rationalPointsContinuousMulEquiv`.
The imported construction `GeneralLinearRationalGraded` supplies the actual
carriers, operators and ring objects; it does not itself establish this
proposition. The intended exact reuse bridges require separate proof
publication and independent review.

The source's printed tensor identification on p. 2184 is read as the
Grothendieck group of the product Levi, with induction mapping to the
larger GL group. Induction compatibility refers to Théorème 1.7(2).
In Théorème 2.3 the monomials in segment classes form the additive basis;
the segment generators alone do not. These are the corrections recorded
in the registered Aubert audit and citation guide. The general corrected
complex and the unresolved Proposition 3.2 are not proof inputs asserted
by this statement module.

No classification-independence claim is made. The existing matrix proofs
and helper declarations retain their own representation-theoretic
dependencies; the program's final declaration-level ledger must account
for their actual transitive uses, as well as `hx`, `hl` and `hp`.
