# Graded exact K0 of actual rational-point general linear groups

This is an internal transport construction in
`Langlands.Aubert.General.RationalPointFamily.GL`. It reuses the current
matrix-group constructions by their Lean names, along the published canonical
continuous group equivalence
`GroupScheme.GeneralLinear.rationalPointsContinuousMulEquiv`.
It is not a new translation of a literature statement. Aubert's 1995
Définition 2.1 and Théorème 2.3 motivate the subsequent comparison target;
this module itself constructs the objects needed to state that target.

## Groups, topology and universes

Fix `p`, `[Fact p.Prime]`, `F : PadicField.{u} p` and
`T : F.TopologicalData`. This GL specialization uses p-adic fields, matching
the existing matrix GL development. It does not replace the arbitrary
nonarchimedean local fields of the general reductive program.

`RationalGeneralLinear F N` is the rational-point group of the actual group
scheme `GL_(Fin N)` over `F.Carrier`, for every natural `N`, including zero.
`rationalGLTopology F T N` is its evaluation topology `pointTopology`,
using `T.topology` and the topological-ring instance obtained from
`T.valuativeRel` and `T.localField`.
The carrier universe of representations is `max (u + 1) v`, where `v` is
independent of the field universe `u`.

`RationalGLK0 F T N` is
`SmoothRep.FiniteLengthGrothendieckGroup` of actual smooth complex
representations of that topological rational-point group. Its relations are
those of all actual finite-length short exact sequences; it is not defined as
a free group on formal labels.
`rationalGLPullbackEquiv` is the published exact-K0
`FiniteLengthGrothendieckGroup.pullbackEquiv` for the canonical continuous
group equivalence from rational points to matrices. Its direction is from
matrix K0 to rational-point K0, because representations pull back.

## Rankwise operators and support signs

`rationalUnadjustedOperator` and `rationalAdjustedOperator` conjugate,
respectively, `Aubert.alternatingOperator` and `Aubert.adjustedOperator`
by `rationalGLPullbackEquiv`. These definitions have no extra representation
premise beyond the published constructions they import.
The identification of the first with the literal rational standard-family
alternating operator is a separate target using the published
`rationalAlternatingOperatorComparison`; it is not built into the definition.

`rationalSupportSign` accepts an actual rational-point smooth module and a
proof that it is irreducible. It pulls the module to the matrix group by the
inverse continuous equivalence, transports irreducibility by
`Langlands.isIrreducible_comp_continuousMulEquiv_iff`, and applies
`Aubert.supportSign` to that actual irreducible isomorphism class.
Thus its convention is exactly the support sign already defined in
`SupportSign`, rather than a new sign convention. The formula relating the
adjusted and unadjusted operators on actual irreducible classes is a separate
proposition target.

## Graded construction

| Declaration | Construction |
| --- | --- |
| `RationalGradedGrothendieckGroup` | The direct sum of `RationalGLK0` over every natural rank. |
| `rationalGradedInclusion` | The canonical homogeneous inclusion `DirectSum.lof`. |
| `rationalGradedPullbackEquiv` | `DirectSum.congrLinearEquiv` of the rankwise pullback equivalences. |
| `rationalGradedAdjustedOperator` | Conjugation of the whole `Aubert.gradedAdjustedOperator` by that direct-sum equivalence. |
| `rationalGradedMultiplication` | Bilinear conjugation of `Aubert.gradedMultiplication`; the original exact-K0 additive groups are retained. |
| `rationalGradedUnit` | The image of `Aubert.gradedUnit`, the actual trivial line in rank zero. |
| `rationalGradedInductionRing` | The commutative ring with that multiplication and unit on the existing additive group. |
| `rationalGradedRingEquiv` | The canonical matrix-to-rational-point ring equivalence with underlying additive equivalence `rationalGradedPullbackEquiv`. |
| `rationalSegmentPolynomialEquiv` | Composition of `Aubert.segmentPolynomialEquiv` with `rationalGradedRingEquiv`. |
| `rationalSegmentMonomialBasis` | Image of the complete `Aubert.segmentMonomialBasis` under `rationalGradedPullbackEquiv`. |
| `rationalZelevinskyEndomorphism` | Ring conjugation of `Aubert.zelevinskyEndomorphism`. |

The last three declarations concern the entire graded group or ring, rather
than only its segment generators. The basis index is
`T.Segment.{max (u + 1) v, u} →₀ ℕ`: finite monomials in all segment
variables, including the empty monomial.

## Visible prerequisites and intrinsic laws

The declarations retain the following matrix-side propositions at carrier
universe `max (u + 1) v`.

* `hx : Aubert.BinaryProductExactnessStatement F T` is required by
  multiplication and all ring and polynomial constructions. It asserts
  preservation of finite-length short exact sequences in each variable of
  the actual normalized binary product. Finite-length preservation itself is
  supplied by the published `binaryProduct_preservesFiniteLength`.
* `hl : Aubert.GradedInductionRingLawsStatement F T hx` is additionally
  required by the ring and polynomial comparisons. It asserts associativity,
  commutativity and the two unit laws for the constructed matrix multiplication.
* `hp : Aubert.SegmentPolynomialComparisonStatement F T hx hl` is
  additionally required by the polynomial equivalence, monomial basis and
  Zelevinsky endomorphism. It is the whole polynomial comparison, with the
  actual segment classes, and is not replaced by a generator calculation.

The rankwise operators, support sign, additive graded equivalence and graded
adjusted operator do not take `hx`, `hl` or `hp`.
The graded unit does not take these premises either.

The ring constructor proves its intrinsic laws by applying the inverse
additive equivalence, canceling the two transports, and using the appropriate
component of `hl`. Additivity, zero multiplication and distributivity are
supplied by bilinearity of the transported multiplication.
The ring equivalence's multiplication law cancels the same inverse transports.
The polynomial equivalence and basis then use the published whole matrix
comparisons directly. None of these intrinsic transport laws discharges
`hx`, `hl` or `hp`.

## Scope

This definition unit makes no unconditional Theorem 2.3 claim. A separate
Prop-valued target must identify the literal rational standard-family operator,
give the support-sign formula on actual irreducible modules, and prove
multiplicativity, unit preservation, involutivity and equality with the
transported Zelevinsky endomorphism on the whole graded group. Its exact proof
requires its own publication and independent review. Completion of the parent
program still requires the representation-theoretic prerequisites and their
declaration-level dependency ledger.
