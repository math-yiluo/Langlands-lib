# Aubert Theorem 2.3 on actual GL rational points

Authors: Worker 3640 (Lean proof and Markdown draft); Worker 436 (current-base
verification, dependency remeasurement and submission).

`Langlands.Aubert.General.RationalPointFamily.GL.rationalTheorem23.{u, v}`
proves exactly `RationalTheorem23Statement.{u, v}` from
`GeneralLinearRationalTheorem23Statement`. The theorem adds no parameter or
hypothesis to that aggregate proposition. It applies to all the actual
rational-point groups, topologies and representation universes of that target,
including rank zero. The field is the existing `PadicField.{u} p`, with its
supplied `TopologicalData`; this is the GL specialization, not an extension
to the general program's arbitrary nonarchimedean local fields.

The exact finite-length Grothendieck groups retain relations from all actual
short exact sequences. All comparisons use the continuous multiplicative
equivalence from actual rational points of the GL group scheme to the matrix
group, and its contravariant pullback on exact K0. Representations have carrier
universe `max (u + 1) v`, with independent `u` and `v`.

## Implemented proof

Write `e_N` for `rationalGLPullbackEquiv F T N`, from matrix exact K0 to
rational-point exact K0. The rational unadjusted and adjusted operators are
conjugates of their matrix counterparts by `e_N`. The graded equivalence `e`
is their direct sum, preserving the rank index. The rational induction ring
is transported by the same equivalence.

**Literal operator identification.** The private linear-algebra helper
`conjugate_eq_of_intertwines` proves that `e_N D = R e_N` implies
`e_N D e_N⁻¹ = R`: apply the intertwining equation to `e_N⁻¹ x` and cancel
the equivalence. `rationalUnadjustedOperatorIdentification` applies this to
`rationalAlternatingOperatorComparison`. It keeps the published theorem's
local compactness, nonarchimedeanity and Hausdorff conclusions; the existence
of closed unipotents and parabolics, continuous projections, compact-limit
properties and functor finite-length premises; and its quantification over
arbitrary witnesses of those premises. Thus the transported operator agrees
with the literal rational standard-family alternating sum, rather than only
with a relabelled matrix expression.

**Support adjustment.** For an actual rational-point irreducible module `E`,
pull back along the inverse group equivalence to a matrix module `M`.
`isIrreducible_comp_continuousMulEquiv_iff` supplies irreducibility of `M`,
and `hasFiniteLength_of_isIrreducible` supplies its finite length.
`FiniteLengthGrothendieckGroup.pullback_ofRepresentation` identifies the
inverse image of the exact class of `E` with the exact class of `M`.
Apply `Aubert.adjustedOperator_irreducible` to that class and move the integer
scalar through `e_N`. The inherited definition of `rationalSupportSign`
is precisely the resulting sign. The second clause applies
`Aubert.supportSign_of_support` to every supplied actual quasicuspidal block
support presentation of `M`. It gives `(-1)^(N - B.length)` without requiring
a new support presentation or selecting a different witness.

**Rank zero and homogeneous restriction.** The two matrix rank-zero operator
identities, `alternatingOperator_rankZero` and `adjustedOperator_rankZero`,
reduce their conjugates to identity maps by equivalence cancellation.
`supportSign_rankZero` proves the third rank-zero clause. The private
`rationalGradedPullbackEquiv_homogeneous` uses the direct-sum congruence's
value on a homogeneous inclusion. Pull a homogeneous rational class back
through the surjective `e_N`, apply
`Aubert.gradedAdjustedOperator_homogeneous`, and transport the result by `e`.
This proves the restriction for every homogeneous K0 class, not just object
generators.

**Signed segment exchange.** Given the target's actual strong segment socle
and special quotient, their supplied strong relations imply irreducibility
and hence finite length. The exact-class pullback formula identifies their
actual rational-point classes with `e_N` applied to the matrix classes.
The published `Aubert.segmentSocleHead` gives the unadjusted formula with
sign `(-1)^(Δ.degree - Δ.length)`. Linearity of `e_N` transports it to the
required rational-point class formula. No isomorphism of arbitrary modules
is inferred from equality of their Grothendieck classes.

**Whole graded ring.** For arbitrary supplied matrix premises `hx`, `hl`,
`hp`, install the two actual induction rings and let `e` be
`rationalGradedRingEquiv`. The three conclusions of
`Aubert.aubertTheorem23` give matrix multiplicativity, Zelevinsky
involutivity and equality of the complete matrix linear maps. Transport
multiplicativity through `e`, using the multiplication laws of the ring
equivalence. Transport unit preservation from
`Aubert.gradedAdjustedOperator_unit`. Cancel consecutive `e⁻¹ e` in the two
involutivity equations; the adjusted case uses `Aubert.adjustedInvolutivity`,
and the Zelevinsky case uses the matrix theorem's involutivity conclusion.
Apply linear-map extensionality to the matrix whole-map equality for the
fifth clause. The sixth clause is the definition of the transported whole
polynomial equivalence. The seventh rewrites by
`Aubert.segmentMonomialBasis_apply` and the definition of a transported
basis. These formulas cover every polynomial and every finite segment
multiplicity function, including the empty monomial. The whole-map equality
therefore retains the full polynomial comparison `hp`, rather than replacing
it with an unsupported generator argument.

Finally `rationalTheorem23` assembles the literal identification and the five
remaining component proofs under exactly the field, topology and
`hx`, `hl`, `hp` quantifiers of the target.

## Published witnesses for the matrix premises

The supporting theorem `rationalWholeGradedTheorem23Canonical` supplies all
three premises at universes `u, max (u + 1) v`:

| Parameter | Exact Library theorem used |
| --- | --- |
| `hx` | `Langlands.Aubert.binaryProductExactness F T` |
| `hl` | `Langlands.Aubert.gradedInductionRingLaws F T hx` |
| `hp` | `Langlands.Aubert.segmentPolynomialComparison F T hx hl` |

It applies `rationalWholeGradedTheorem23` to these witnesses. Its only
parameters are the prime, primality instance, field and supplied topology;
there is no remaining binary-exactness, ring-law or polynomial-comparison
hypothesis in this specialization. The aggregate theorem still works for
arbitrary supplied witnesses, as its published target requires.

This specialization deliberately uses the published polynomial-comparison
proof. That proof applies
`Langlands.Aubert.SegmentPolynomialSurjectivity.segmentPolynomialComparison_of_socleExhaustion`
to `Langlands.Classification.multisegmentSocleExhaustion`. The latter is the
existence part of Zelevinsky 1980, Theorem 6.1(c), on actual segment-socle
products. The polynomial argument also uses the derivative/triangularity
infrastructure described in `SegmentPolynomialComparisonProof.md`.
The ring laws use actual induction associativity and units and the proved
`Classification.twoFactorProductConstituentCommutativity` for positive
commutativity. The exactness proof uses complex tensor exactness and actual
normalized-induction exactness, with full rank-zero tensor carriers.
These are representation-theoretic proofs, not structural assumptions.

## Dependency and source boundaries

Direct mathematical reuse, apart from the intrinsic equivalence/direct-sum
identities, is recorded by the following declaration names. Names beginning
`Aubert.` are under `Langlands.Aubert`.

| Component | Project proof inputs |
| --- | --- |
| Literal standard-family sum | `rationalAlternatingOperatorComparison` in this GL namespace |
| Exact-class transport | `Langlands.SmoothRep.FiniteLengthGrothendieckGroup.pullback_ofRepresentation` |
| Irreducibility transport | `Langlands.isIrreducible_comp_continuousMulEquiv_iff` |
| Support adjustment and its exponent | `Aubert.adjustedOperator_irreducible`, `Aubert.supportSign_of_support` |
| Rank zero | `Aubert.alternatingOperator_rankZero`, `Aubert.adjustedOperator_rankZero`, `Aubert.supportSign_rankZero` |
| Homogeneous restriction | `Aubert.gradedAdjustedOperator_homogeneous` |
| Signed segment exchange | `Aubert.segmentSocleHead` |
| Whole comparison | `Aubert.aubertTheorem23`, `Aubert.gradedAdjustedOperator_unit`, `Aubert.adjustedInvolutivity`, `Aubert.segmentMonomialBasis_apply` |
| Canonical supplied premises | `Aubert.binaryProductExactness`, `Aubert.gradedInductionRingLaws`, `Aubert.segmentPolynomialComparison` |

This is an internal transport and assembly of existing results, with no new
source translation or external mathematical axiom. Its source motivation
and corrections are the same as the target: Aubert 1995, Definition 1.5,
p.2181; Definition 2.1 and Remark 2.2, p.2184; Theorem 2.3, p.2185. The
registered source `aubert-1995-duality` has SHA-256
`57af9c46769f6edd8e142ddaf465e89acfa2f2147db222d26879a28a06df9693`.
The tensor product corresponds to the product Levi; induction maps to the
larger GL group, and its source identity is Theorem 1.7(2). The complete
segment-monomial basis, not the generators alone, provides the additive
basis in the source argument.

The actual proof inherits the matrix results' transitive support, segment,
finite-length and classification-module dependencies. In particular the
canonical supplied-premise theorem explicitly uses Zelevinsky multisegment
socle exhaustion through `segmentPolynomialComparison`. No classification
independence is asserted. The existing separate inventory for the literal
rational unadjusted comparison concerns that smaller root only; it cannot
be substituted for the dependencies of this whole theorem. General
reductive identities, the corrected general smooth complex and its
irreducible consequences remain separate obligations of the parent.

For dependency accounting, a private development traversal at the
submission base, Library commit `c40a01345b2f4172fa41e07ff31644b40e695003`,
with this proof module, followed the types and values of project constants,
including theorem values. It classified constants by their defining module,
counted a constant as project-defined when its module lies under `Langlands`,
and stopped outside the project. "Classification modules" are those under
`Langlands.Representation.Classification`. The following counts distinguish
the arbitrary-premise aggregate from the specialization supplying the three
premises:

| Root in this namespace | Project constants | Project modules | Constants from classification modules | Theorems among those constants |
| --- | ---: | ---: | ---: | ---: |
| `RationalTheorem23Statement` | 34,973 | 2,811 | 353 | 260 |
| `rationalTheorem23` | 36,311 | 2,940 | 437 | 321 |
| `rationalWholeGradedTheorem23Canonical` | 20,447 | 1,417 | 2,930 | 2,423 |

The union of the two proof closures contains 46,147 project constants in
3,467 modules, including the same 2,930 classification-module constants
and 2,423 theorems. These figures equal those of an earlier traversal at
Library commit `430cc03fe803c5dbf74bc3baf91e8f7a2c26ea9c`. They are
declaration-dependency measurements, not import counts or counts of
applications of a classification theorem.

The same traversal tested membership of named constants. The closure of
`rationalWholeGradedTheorem23Canonical` contains
`Langlands.Classification.multisegmentSocleExhaustion`,
`Langlands.Aubert.segmentPolynomialComparison`,
`Langlands.Aubert.gradedInductionRingLaws` and
`Langlands.Aubert.binaryProductExactness`. The closure of the
arbitrary-premise `rationalTheorem23` contains none of these four, because
those premises are its parameters, but it contains
`Langlands.Aubert.aubertTheorem23` and `Langlands.Aubert.segmentSocleHead`.
Both proof closures, and that of the target statement, contain
`Langlands.Classification.twoFactorProductConstituentCommutativity`.
The semantic use of Zelevinsky Theorem 6.1(c) is the explicit exhaustion
application recorded above; no absence of a particular name is used to
infer independence of the matrix results that the aggregate does use.
