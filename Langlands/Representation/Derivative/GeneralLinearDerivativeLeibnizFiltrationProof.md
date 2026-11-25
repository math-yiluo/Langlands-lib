# The actual derivative Leibniz filtration in every rank

The theorem `Langlands.Derivative.generalLinearDerivativeLeibnizFiltration`
proves the unchanged Library proposition
`Langlands.Derivative.GeneralLinearDerivativeLeibnizFiltrationStatement`.
Its complete outer telescope is

```lean
{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
  GeneralLinearDerivativeLeibnizFiltrationStatement.{uF, uV} F T
```

The universes `uF` and `uV` are independent. There is no additional premise.
The proof installs the supplied topology through the existing constructions;
it makes no choice of a canonical topology.

## The exact conclusion

For every bundled continuous nontrivial unitary additive character `ψ`, every
`a b d : ℕ` and every `hd : d ≤ a + b`, the source is literally

```text
T.binaryNormalizedProductFunctor a b ⋙
  generalLinearDerivative T ψ (a+b) d hd ⋙ SmoothRep.toRep.
```

Its domain is the entire product category of smooth representations of
`GL_a` and `GL_b`, with input-carrier universe `uV`; its values have carrier
universe `max uF uV`. The result supplies an equivalence
`e : LeibnizIndex a b d ≃ Fin (leibnizIndices a b d).card` and an
`IsGluedFrom` assertion with pieces `leibnizPiece T ψ a b d (e.symm i)`.
The finite set is precisely

```text
{(i,j) : i ≤ a, j ≤ b, i+j=d}.
```

At `(i,j)` the piece applies the actual order-`i` and order-`j` factor
derivatives, their actual normalized binary product, the prescribed smooth
`generalLinearRankCast` along
`(a-i)+(b-j)=(a+b)-d`, and only then `SmoothRep.toRep`.
There is no residual character twist.

By the definition of `IsGluedFrom`, this is an actual finite chain of
subfunctors from zero to the literal source, preserved by every pair of
input intertwiners, with natural isomorphisms from the successive quotient
functors to the specified pieces, up to permutation. Every feasible index
occurs exactly once. Equal, isomorphic and zero pieces at different indices
remain separate grades. The existing statement's `.filtration` extractor
can absorb the permutation into `e`; that conditional extractor is not
used to establish the theorem.

## Original source and conventions

The registered original is I. N. Bernstein and A. V. Zelevinsky,
*Induced representations of reductive p-adic groups I*, Ann. Sci. ENS
(4) 10 (1977), 441–472, literature ID
`bernstein-zelevinsky-1977-induced-i`, PDF SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.

| Original passage | Role in the implemented argument |
| --- | --- |
| §1.8 and Proposition 1.9(g), printed pp.444–445, one-based PDF pp.5–6 | Normalized induction/localization conventions and commutation with an inert tensor factor. The arbitrary-carrier tensor commutations used here are proved by explicit quotient maps in Lean. |
| §§3.2–3.5, printed pp.450–452, PDF pp.11–13 | Normalized minus functors, their exactness and iterated derivatives. Only independently proved Library exactness is used. |
| §4.3, printed p.454, PDF p.15 | Order-zero GL derivative is the identity; positive GL derivatives are positive derivatives after mirabolic restriction. |
| §4.12, printed p.457, PDF p.18 | Binary and left/right mixed products, including the separate case (III) epsilon character. |
| Proposition 4.13(a–c) and Corollary 4.14(a–c), printed p.458, PDF p.19 | Restriction sequence, mixed derivative comparisons and the Leibniz assertion. The printed proof obtains (c) from (a), (b) and 4.13(a), which is the positive-rank route implemented here. |

Corollary 4.14(c), also identified there with Lemma 4.5, is the
positive-rank source assertion. The source convention `P_s` for positive
`s` is the Library group `GeneralLinear.mirabolic (s-1) F.Carrier`.
Only those groups occur; the implementation introduces no `P_0`.
Above-rank mirabolic derivatives are handled by a proved subsingleton
carrier result at valid total orders.

The arbitrary `GL_0`-carrier cases are an internal extension. They use
the actual tensor model of the rank-zero binary product, rather than
replacing a rank-zero representation by a scalar or a tensor unit.
The finite feasible subtype, equality-based rank transports, whole-functor
filtrations and their enumeration are also internal formalization choices.
They retain the source's graded products and strengthen the packaging to
naturality on the full product category.

A bounded check of the declared source and reading locations found no
applicable registered BZ77 errata entry, including no source-specific
`notes/errata/bernstein-zelevinsky-1977-induced-i.md`. This records the
local check, not a global absence claim.

## Implemented proof

The entry theorem introduces `ψ a b d hd` and splits first on `d`, then
on `a`, then on `b`. These are exhaustive cases of the unchanged proposition.

### Order zero

`generalLinearDerivativeLeibnizFiltration_zero` applies for every `a,b`.
Both factor derivatives and the source derivative are identity functors;
the rank cast is the identity. The complete feasible set is `{(0,0)}`.
The actual flag is zero followed by the whole source subfunctor. Its
quotient is full modulo zero, naturally isomorphic to the source and hence
to the unchanged piece. `Finset.equivFin` enumerates the singleton.
This uses the proved generic one-step quotient construction, not a
positive-order derivative assertion.

### Either input rank zero

For positive order, if `a=0`, the theorem applies
`generalLinearDerivativeLeibnizFiltration_left_zero`. If `a>0` and `b=0`,
it applies `generalLinearDerivativeLeibnizFiltration_right_zero`.
The helper theorems themselves also include order zero.
Their complete feasible sets are `{(0,d)}` and `{(d,0)}`.

The published `LeibnizRankZeroBoundary` comparisons identify the actual
source with its single piece naturally in both inputs. The right-zero
comparison uses `ZeroRankTensor.generalLinearDerivativeTensorIso`.
On a character-localization quotient its maps are
`[v ⊗ w] ↦ [v] ⊗ w` and the inverse on generators. They descend through
the entire relation span, are inverse, and commute with the group action,
both input maps, pullbacks, determinant twists and rank casts. Iteration
commutes every Phi step and the final Psi step with the arbitrary inert
factor. The binary-right-zero tensor comparison gives the required
binary endpoint. For a zero first factor, the actual binary tensor
swap moves it to the right, the derivative comparison is applied, and
the inverse swap restores the order. The published rank-cast composition
laws retain the exact prescribed output group.

`LeibnizRankZeroGluing` packages these natural isomorphisms using the
actual one-step filtration and the complete singleton enumeration.
Neither rank-zero carrier is chosen or assumed one-dimensional.

### Positive ranks and positive order

Put `a=m+1`, `b=n+1`. The final branch calls
`generalLinearDerivativeLeibnizFiltration_pos`, supplying all three of its
explicit arguments from the published unconditional theorems

```text
leftMixedProductDerivativeIso F T
leftMixedProductDerivativeVanishing F T
rightMixedProductDerivativeFiltration F T.
```

Thus the final theorem has no remaining theorem-valued hypothesis.
In particular, the conditional positive assembly alone would not prove
the target; each of its three premises is discharged here.

The assembly performs the following actual construction.

1. The published `leibnizRestrictionDerivativeExact` supplies natural
   arrows `S ⟶ leibnizSource T ψ (m+1) (n+1) d hd ⟶ Q` with
   objectwise injectivity, middle exactness and surjectivity.
   Before differentiation these are the actual open-orbit inclusion
   and closed-orbit restriction of 4.13(a):
   `0 → (A|P) × B → (A × B)|P → A × (B|P) → 0`.
   The published derivative exactness theorem applies the actual
   positive derivative to these arrows; the source and rank comparisons
   make its middle literally `leibnizSource`.
2. Apply `rightMixedProductDerivativeFiltration` at GL rank `k=n+1`,
   mirabolic index `r=m` and order `d`. Precompose with
   `generalLinearRestriction T m × 𝟭`, and transport the output rank.
   The published `leibnizPositivePieceIso` identifies each resulting
   grade with the unchanged Leibniz piece at `(j,t)`, where
   `1 ≤ j ≤ m+1`, `t ≤ n+1`, `j+t=d`.
   These are exactly all positive-first indices.
3. If `d ≤ n+1`, apply `leftMixedProductDerivativeIso` at `k=m+1`,
   `r=n`, order `d` to the quotient. The published
   `leibnizRestrictionQuotientPieceIso` combines this comparison with
   positive-GL restriction/derivative compatibility and the smooth
   rank transports. It gives `Q ≅ leibnizPiece ... (0,d)`.
   The quotient flag is the actual one-step flag.
   If `n+1<d`, `leftMixedProductDerivativeVanishing` at the same ranks
   gives subsingleton carriers for `Q`. The proved
   `leibnizRestrictionQuotient_subsingleton` transfers that result to
   the literal quotient functor. Its flag has length zero, using the
   proved generic `Filtration.ZeroLength` construction. Exactly in this
   case the zero-first index is absent.
4. `IsGluedFromFamily.splice` joins the two flags along the displayed
   short exact sequence. The underlying `Filtration.Splicing`
   construction uses images of the subobject flag and inverse images
   of the quotient flag, with actual quotient isomorphisms. All maps
   are natural, so the result is a subfunctor flag of the literal
   middle functor.
5. `leibnizIndexSplitEquiv m (n+1) d` is a bijection from the sum of
   `RightMixedDerivativeIndex (n+1) m d` and `PLift (d ≤ n+1)` to the
   full `LeibnizIndex (m+1) (n+1) d`. The first summand keeps `(j,t)`;
   the optional second summand maps to `(0,d)`. The families agree
   with the unchanged pieces at this bijection, so reindexing drops
   no zero or repeated grade. `exists_equiv` and `Fintype.card_coe`
   give the exact exterior enumeration of the target.

At top order `d=a+b`, the feasible set is `{(a,b)}`. The zero-first
quotient block is empty when both ranks are positive. The surviving
piece is the actual binary product on `GL_0` of the two actual top
derivative carriers. Both carriers remain present. At `d=b` the
zero-first block is still present and its second derivative already has
rank zero. No exceptional positivity or nonzero-carrier premise is added.

## Normalization and rank transport

The functors and casts in the target are unchanged. The minus functors
use the inverse-half determinant twist; normalized upper-block induction
uses the positive-half modulus covariance and right translation.
The right mixed product retains the separate case (III) epsilon
character as well as its rectangular half character.

These signs use BZ77's module convention: the module of an automorphism
is the inverse of the scalar for the forward Haar pushforward.
Mathlib's `mulEquivHaarChar φ` satisfies
`mulEquivHaarChar φ • μ.map φ = μ`, so it has the BZ77 module convention.
The published mirabolic Haar-modulus proof identifies this module with
the determinant norm. The mixed-product comparison proofs establish the
complete coefficient-character identities, including the epsilon
factor, before returning their actual natural isomorphisms. The final
assembly transports those isomorphisms and introduces no further twist.

`generalLinearRankCast` acts in the smooth representation category.
The compatibility lemmas compare it with the rank cast after forgetting;
composition and cancellation are equality elimination and functor
associativity. Every piece retains the smooth cast before
`SmoothRep.toRep`, including rank-zero outputs. The supplied `T`, `ψ`
and independent universes are preserved throughout.

## Published mathematical inputs and their proof provenance

All mathematical inputs are imported by Lean name. The following
checks distinguish proved inputs from proposition definitions
and conditional constructions.

| Input | Verified proof |
| --- | --- |
| Full right mixed-product derivative filtration | `rightMixedProductDerivativeFiltration`, proved in `RightMixedProductDerivativeFiltrationProof`. |
| Full left mixed-product derivative formula | `leftMixedProductDerivative` and its `Iso`/`Vanishing` projections, proved in `LeftMixedProductDerivativeProof`. Its proof includes its higher-order and vanishing proof modules. |
| Actual differentiated restriction sequence | Unconditional `leibnizRestrictionDerivativeExact`, proved in `LeibnizRestrictionExact`. |
| Quotient-to-piece bridge | `LeibnizQuotientPiece`, a proved module; its explicit comparison and vanishing data are supplied from the proved left theorem. |
| Positive assembly | `LeibnizPositiveGluing`, a proved module; all three conditional arguments are discharged in this entry. |
| Boundary, tensor, casts, indices, piece comparisons and general filtration operations | Published constructions in the complete closure below. The order-zero, rank-zero, finite-index, one-step, zero-length, transport, reindexing and splicing results are actual proved maps or constructions; none assumes the all-rank assertion. |

The full right and left proofs, including every extra module ported with
them, and the quotient bridge were compared
against the audited Library tree. Both Lean and Markdown
bytes agree. The source assertions themselves supply no
unproved premise.

The mathematical trace through the lower inputs is as follows.

| Branch or potentially broad import | Actual mathematical dependencies |
| --- | --- |
| Restriction sequence | The actual two-orbit matrix geometry, stabilizers, coefficient transports and closed-subgroup Mackey filtration give open inclusion and closed restriction. Closed-orbit section extension uses finite clopen compact-section gluing. Parabolic quotient compactness uses integral compact subgroups and the elementary Iwasawa column-reduction argument; it identifies compact and smooth induction. No segment geometric-lemma consumer is assumed. |
| Minus and derivative exactness | `MirabolicMinusExactnessProof` applies character-localization exactness along the closed radical, using upper-unipotent compact containment. Finite compact-orbit averaging proves injectivity; relation-span quotient algebra proves middle exactness and surjectivity. Compactness and smooth stabilizers make the averaging orbits finite; no finite-dimensionality or finite-length theorem is needed. `GeneralLinearDerivativeExactnessProof` iterates the two actual normalized minus functors. |
| Left mixed derivatives | The published left Psi comparison identifies the entire localized compact induction by radical projection, normal-coinvariant comparison, split quotient, character twist and the positive binary compact comparison. The left Phi comparison uses actual two-orbit Mackey restriction, quotient right exactness, full localized-cycle vanishing, positive-character stages and complete determinant-character identities. Higher orders induct on Phi steps with actual source/output casts. The P₁ boundary kills the entire carrier by the nontrivial character; high-order vanishing propagates through the remaining functors. |
| Right mixed derivatives | The positive-rank proof inducts on the mirabolic index. Order one uses the published right Psi comparison. Higher orders use the actual right Phi short exact sequence, transport it through the remaining exact derivative and splice the inductive subobject flag with the quotient flag supplied by the proved left theorem. The P₁ case uses the published right Phi boundary comparison. GL₀ uses whole-group compact-induction evaluation and the arbitrary tensor quotient maps. No general GL Leibniz theorem enters this earlier right theorem. |
| Generic filtration algebra | `OneStep`, `ZeroLength`, `QuotientFirstIso`, `Splicing`, `Reindexing`, `Precomposition` and `GluedFamily` operate on invariant submodules and actual quotient functors. First-isomorphism maps, images and inverse images give their grade comparisons. They have no derivative, classification or finiteness conclusion among their premises. |
| Rank-zero tensor and all rank comparisons | Explicit quotient/tensor maps, tensor symmetry, whole-group evaluation, pullback/twist functor laws, equality transport and natural-number arithmetic. Arbitrary carriers remain arbitrary. |
| `Classification.Supercuspidal`, `SupercuspidalContragredientAux`, `SupercuspidalContragredientStatement` | These enter conservatively through smooth small-realization/countability infrastructure. Their bodies provide the admissibility/Jacquet-vanishing predicate, class packaging, equivalence invariance, conjugate-coinvariant equivalence and conditional transfer interfaces. They contain no excluded classification or exhaustion proof and supply no derivative-comparison premise. The countability input used below is proved from finite matrix products, unit embeddings and local compactness. |
| `LevelCalculus` and derivative detection | The right mixed proof uses its exactness-composition theorem with the proved minus exactness clauses. Its conservative imports include `MirabolicDerivativeDetectionProof` and `MirabolicDerivativeVanishing`. Their independent rank induction comes from `MinusVanishing` and finite Fourier averaging, the general BZ77 3.8 route; it does not use Whittaker coinvariant finiteness or a mirabolic finite-length consumer. Detection is not an additional premise of this final theorem. |
| `Homogeneity`, `Category.Basic` and finite-length imports | These provide the order wrapper, rank casts, zero-carrier laws and finite-length predicates or general module algebra. No segment homogeneity theorem or representation finite-length conclusion supplies a proof input. |
| Whittaker, Rankin–Selberg and harmonic-analysis modules | These supply elementary characters and function models, Iwasawa compactness, Haar scaling and quotient measures, local sections, cutoff, compact-orbit averaging and unimodularity. No prohibited irreducible, Levi-cuspidal, supercuspidal or all-character coinvariant-finiteness theorem is used. |
| Statement modules | They fix the exact functor/proposition types. The only mixed assertions used are supplied by their unconditional published proofs. Other clauses and conditional `.filtration` extractors provide no proof input. |

## Condition-by-condition inherited independence audit

Each exclusion here applies to the named conclusion, its proofs
and every downstream consequence, directly and transitively. Repeated
conditions inherited through several consumers retain their full scope.
The complete import closure was scanned for the excluded declaration names,
with no Lean-code matches. The body and
provenance audit above checks the mathematical route as well; a name scan
alone would not establish independence.

| Inherited condition or excluded result | Audit finding |
| --- | --- |
| Actual natural filtration, complete feasible enumeration, repeated/zero grades, unchanged target and imports | The displayed differentiated sequence and generic splice construct the actual flag. The index-split equivalence covers precisely all feasible pairs, including zero pieces. Only this final Lean/Markdown pair is new; the statement and all imported pairs are unchanged. |
| All ranks, order zero, top order, arbitrary GL₀ carriers, independent universes, supplied topology/character, no extra object hypotheses | The exhaustive case split and boundary constructions above cover these cases. No admissibility, irreducibility, finite dimension/length, genericity, nonzero or chosen vector, universe saturation or theorem-valued premise remains. |
| Only proved and published upstream inputs | The two full mixed proofs discharge the positive helper's premises. Restriction, exactness, tensor and general filtration operations are published proved constructions. No citation, proposition definition, unproved statement or conditional consumer supplies a missing proof. |
| `UnlinkedSegmentSocleProductIrreducible`, `LinkedSegmentSocleReverseProductStructure`, `LinkedSegmentSoclePairReducible` | No segment product structure or reducibility theorem occurs in the closure or the mathematical route. |
| `JuxtaposedSegmentSocleReverseProductStructure`, `LinkedSegmentSocleReverseProductQuotientHom` | No such structure or quotient-Hom conclusion supplies an input. The quotients here are explicit general module quotients. |
| `SegmentSocleProductIrreducibility` | No criterion or consequence of it is used; the construction applies to arbitrary smooth representations. |
| `AdjacentUnlinkedSegmentSocleSwap` and `TwoSegmentSocleCommutation` | Neither the adjacent commutation, its proof, nor the two-segment commutation results is used. The GL₀ swap is the elementary tensor flip. |
| `LinkedSegmentSocleGluing` | No linked gluing is used. The splice here is general short-exact-sequence filtration algebra. |
| `OrderedMultisegmentSocleExistence` and socle exhaustion | No ordered existence, essential-subobject or exhaustion conclusion enters. |
| Individual special-head/reverse-socle and segment-socle/reverse-head existence | Neither existence result supplies any premise. No segment or head/socle module occurs. |
| Every segment derivative formula and clauses (b), (d), (e), (f) of the six derivative statements of `Classification.SegmentSocleDerivativesStatement` | None is used. The derivatives and all mixed comparisons are general BZ77 constructions for arbitrary smooth inputs; no segment formula is an upstream hypothesis. |
| `SegmentFullJacquetFormula`, `SegmentHeadJacquetFormula`, `SegmentSocleJacquetFormula`, `SegmentSpecialJacquetExponentNormFormula` | No such formula is used. General Jacquet quotient exactness and compact character averaging do not depend on them. |
| Analytic segment classification and forward `SegmentSpecialEssentialSquareIntegrability` | No such result supplies an input. |
| `SegmentHeadProductIrreducibility` and `GenericSegmentProductUniqueness` | No conclusion of either enters. Neither genericity nor a product irreducibility criterion appears among the proof's premises. |
| Special-head multisegment exhaustion, ordered strong-head existence, quotient coverage, ordered conversion | No such conclusion is used. Finite enumeration here concerns derivative orders, not representation coverage. |
| Tempered uniqueness and `SquareIntegrableLanglandsClassification` | No such conclusion enters. The incidental supercuspidal-definition imports above provide no classification theorem. |
| Square-integrable and regular exhaustion | Neither supplies a proof input. |
| `TwoSupercuspidalNonadjacentProductIrreducible` and `TwoSupercuspidalProductStructure` | No conclusion of these or of the full-product assembly `TwoSupercuspidalProductStructureProof` enters. This general theorem is upstream of those consumers. |
| Ze80 §§3.5/9.6 segment derivatives, 4.2/9.7 criteria, 9.3 analytic/square-integrability results, classification or exhaustion; circular linked-pair converse | No Ze80 result is a proof input. The positive-rank source route is the independently proved general BZ77 restriction and mixed-minus route. |
| `IrreducibleCoinvariantFinitenessStatement`, `LeviCuspidalCoinvariantFinitenessStatement`, `SupercuspidalCoinvariantFinitenessStatement`, all-character single-block finiteness | None is imported or used. This covers their proofs and downstream consequences. |
| Dependent mirabolic finite-length route | No mirabolic finite-length proof is used. Minus exactness uses compact finite-orbit means on arbitrary smooth carriers. The conservative detection import has the independent general rank/Fourier proof described above. |
| Consumer assemblies, including `TwoBlockDerivativePieces` and zero-factor/unit/two-block-shape helpers | No such assembly or its conclusion proves an upstream input here. All conditional arguments actually used are discharged by the published full general mixed theorems. |

## Complete direct and transitive import inventory

At audited Library commit `abc2300bb37d2121fc402c9bbd15b8a9b51f529d`,
recursive traversal of every project import gives 323 project modules
including this entry, hence 322 published dependencies. All 644 dependency
Lean/Markdown files are nonempty and byte-identical to that Library tree.
There is no unpublished dependency, missing pair or modified imported pair.
The exact target pair and everything it imports are unchanged.

The five direct imports are:

- `Langlands.Representation.Derivative.GeneralLinearDerivativeLeibnizBoundary`
- `Langlands.Representation.Derivative.LeibnizRankZeroGluing`
- `Langlands.Representation.Derivative.LeibnizPositiveGluing`
- `Langlands.Representation.Derivative.LeftMixedProductDerivativeProof`
- `Langlands.Representation.Derivative.RightMixedProductDerivativeFiltrationProof`

There is no direct external import in the entry. The complete project
inventory below includes the entry; each prefix followed by suffixes
expands to exactly the corresponding full module names.

- `Langlands.Analysis.Local`: `CompactOpenCoverUnimodularityProof`, `CompactOpenCoverUnimodularityStatement`, `ModularCompactAverage`, `QuotientAutomorphismProof`, `QuotientAutomorphismStatement`, `QuotientAverageReal`, `QuotientAveragingKernel`, `QuotientComplex`, `QuotientFunctional`, `QuotientMass`, `QuotientMeasure`, `QuotientMeasureExistence`, `QuotientMeasureExistenceStatement`, `QuotientMeasurePrerequisites`, `QuotientPositiveLifting`, `QuotientTopology`, `QuotientTranslation`, `SplitKernelQuotient`.
- `Langlands.Group`: `HaarModulus`.
- `Langlands.Group.GL`: `Basic`, `BlockDeterminant`, `BlockModulus`, `Blocks`, `CompactOpen`, `CountabilityProof`, `CountabilityStatement`, `Maps`, `Mirabolic`, `MirabolicMixedOrbitCoverageProof`, `MirabolicMixedOrbitCoverageStatement`, `MirabolicMixedOrbitData`, `MirabolicMixedOrbitRadicals`, `MirabolicMixedOrbitSectionCoefficients`, `MirabolicMixedOrbitSections`, `MirabolicMixedOrbitSpecializations`, `MirabolicMixedOrbitStages`, `MirabolicMixedProductSubgroups`, `MirabolicModularCharacterProof`, `MirabolicModularCharacterStatement`, `MirabolicModulusProof`, `MirabolicModulusStatement`, `MirabolicOppositeIntersection`, `MirabolicProjection`, `MirabolicRadical`, `Nonarchimedean`, `NonarchimedeanStatement`, `NormalizedCharacter`, `OppositeBlocks`, `Padic`, `PadicBlocks`, `PadicOppositeBlocks`, `PadicUpperUnipotent`, `RankMaps`, `RankReindex`, `ReindexCongr`, `ReverseBlocks`, `TriangularParabolic`, `UpperUnipotent`, `UpperUnipotentCompactContainmentProof`, `UpperUnipotentCompactContainmentStatement`.
- `Langlands.HarmonicAnalysis`: `AlgebraicIntegral`, `AlgebraicIntegrand`, `Basic`, `Conductor`, `HaarConjugacy`, `PadicAdditiveConductorProof`, `PadicHaarScalingStatement`, `PadicLatticeTopology`, `PadicRectangularHaarScalingProof`, `PadicScalarHaarScalingProof`.
- `Langlands.LocalFactor.Harmonic`: `Statement`.
- `Langlands.LocalField`: `Canonical`, `Definitions`, `Topology`.
- `Langlands.LocalField.Normalization`: `Definitions`, `Proof`, `Statement`.
- `Langlands.Representation`: `OrbitSpan`.
- `Langlands.Representation.Category`: `Abelian`, `Basic`, `Subquotients`, `Twist`.
- `Langlands.Representation.Classification`: `Supercuspidal`, `SupercuspidalContragredientAux`, `SupercuspidalContragredientStatement`.
- `Langlands.Representation.Compact`: `Definitions`, `FiniteMean`, `OrbitMeanTranslation`, `ProjectionProof`, `ProjectionStatement`, `SurjectivityProof`, `SurjectivityStatement`.
- `Langlands.Representation.Conductor`: `Congruence`.
- `Langlands.Representation.Derivative`: `GeneralLinearDerivativeExactnessProof`, `GeneralLinearDerivativeExactnessStatement`, `GeneralLinearDerivativeLeibnizBoundary`, `GeneralLinearDerivativeLeibnizFiltrationProof`, `GeneralLinearDerivativeLeibnizFiltrationStatement`, `Homogeneity`, `Iteration`, `LeftMixedProductDerivativeProof`, `LeftMixedProductHigher`, `LeftMixedProductVanishing`, `LeftMixedProductZeroRank`, `LeibnizIndices`, `LeibnizPieceCompat`, `LeibnizPositiveGluing`, `LeibnizQuotientPiece`, `LeibnizRankZeroBoundary`, `LeibnizRankZeroGluing`, `LeibnizRestrictionCompat`, `LeibnizRestrictionExact`, `LeibnizZeroFirstPiece`, `LevelCalculus`, `MinusVanishing`, `MirabolicCharacter`, `MirabolicDerivativeDetectionProof`, `MirabolicDerivativeDetectionStatement`, `MirabolicDerivativeVanishing`, `MirabolicDeterminant`, `MirabolicLatticeBox`, `MirabolicMinus`, `MirabolicMinusExactnessProof`, `MirabolicMinusExactnessStatement`, `MirabolicMixedOrbitCharacters`, `MirabolicPhiMinusMackey`, `MirabolicPlus`, `MirabolicProductMinusBoundary`, `MirabolicProductMinusCompatibilityStatement`, `MirabolicProductMinusLeftPhi`, `MirabolicProductMinusLeftPhiCoefficient`, `MirabolicProductMinusLeftPhiCompactComparison`, `MirabolicProductMinusLeftPhiHaar`, `MirabolicProductMinusLeftPhiHostTransport`, `MirabolicProductMinusLeftPhiIdentityComparison`, `MirabolicProductMinusLeftPhiInductionNormalization`, `MirabolicProductMinusLeftPhiLocalization`, `MirabolicProductMinusLeftPhiMackeyLocalization`, `MirabolicProductMinusLeftPhiNormalization`, `MirabolicProductMinusLeftPhiNormalizedSection`, `MirabolicProductMinusLeftPhiSection`, `MirabolicProductMinusLeftPhiSourceAction`, `MirabolicProductMinusLeftPhiSourceComparison`, `MirabolicProductMinusLeftPhiStagesComparison`, `MirabolicProductMinusLeftPsi`, `MirabolicProductMinusLeftPsiInduction`, `MirabolicProductMinusPhiKernelComparison`, `MirabolicProductMinusRightBoundary`, `MirabolicProductMinusRightPhi`, `MirabolicProductMinusRightPhiAssembly`, `MirabolicProductMinusRightPhiCycle`, `MirabolicProductMinusRightPhiCycleCoefficient`, `MirabolicProductMinusRightPhiCycleGroups`, `MirabolicProductMinusRightPhiIdentity`, `MirabolicProductMinusRightPhiIdentityCoefficient`, `MirabolicProductMinusRightPhiIdentityGroups`, `MirabolicProductMinusRightPsi`, `MirabolicProductMinusRightPsiCoefficient`, `MirabolicProductMinusRightPsiGroups`, `MirabolicProductMinusRightPsiZero`, `MirabolicProductRestriction`, `MirabolicProductRestrictionCasts`, `MirabolicProductRestrictionFactors`, `MirabolicProductRestrictionMackey`, `MirabolicProductRestrictionOrbits`, `MirabolicProductRestrictionStabilizers`, `MirabolicProductRestrictionStatement`, `MirabolicProductRestrictionTransport`, `MixedProductDerivativeStatement`, `MixedProductRankCast`, `OrderRecursion`, `RankCastCompat`, `RightMixedProductDerivativeFiltrationProof`, `RightMixedProductDerivativeFiltrationStatement`, `RightMixedProductDerivativePositive`, `RightMixedProductZeroRank`, `ShortExactFunctorLaws`, `ZeroRankTensor`.
- `Langlands.Representation.Dual`: `Definitions`.
- `Langlands.Representation.Filtration`: `Definitions`, `GluedFamily`, `IsoTransport`, `OneStep`, `Precomposition`, `QuotientFirstIso`, `QuotientTail`, `Splicing`, `Transport`.
- `Langlands.Representation.Filtration.Splicing`: `Basic`.
- `Langlands.Representation.Geometric`: `ClosedSubgroupAssembly`, `ClosedSubgroupDefinitions`, `ClosedSubgroupMackeyProof`, `ClosedSubgroupStatement`, `CompactOrbitRestriction`, `CosetAction`, `CosetOrbitHomeomorph`, `OrbitRestriction`, `OrbitSectionExtensionProof`, `OrbitSectionExtensionStatement`.
- `Langlands.Representation.Induction`: `BinaryPositiveCompact`, `BinaryProduct`, `BlockFactors`, `CharacterTwistProof`, `CompactAutomorphism`, `CompactAutomorphismIntegralProof`, `CompactAutomorphismIntegralStatement`, `CompactCoinvariantBijectivityProof`, `CompactCoinvariantBijectivityStatement`, `CompactCoinvariantIntegral`, `CompactCoinvariantLocalInverseProof`, `CompactCoinvariantLocalInverseStatement`, `CompactLocalSection`, `CompactLocalSectionSpanningProof`, `CompactLocalSectionSpanningStatement`, `CompactLocallyConstant`, `CompactQuotientCutoff`, `CompactQuotientProof`, `CompactSurjectivityProof`, `CompactSurjectivityStatement`, `CompactTransitivityProof`, `CompactTransitivityStatement`, `Definitions`, `InverseTranspose`, `NormalCoinvariantKernelProof`, `NormalCoinvariantKernelStatement`, `NormalCoinvariantMap`, `NormalCoinvariantProof`, `NormalCoinvariantStatement`, `NormalSplitComparison`, `OppositeParabolic`, `Parabolic`, `SplitKernelCharacter`, `SplitKernelCharacterExtension`, `SplitKernelCompact`, `SplitKernelCovariance`, `SplitKernelEquivariant`, `SplitKernelHaarTrivial`, `SplitKernelIntegral`, `SplitKernelLocalizationData`, `SplitKernelSectionAction`, `SplitQuotientProof`, `SplitQuotientStatement`, `SplitStagesCharacterComparison`, `SplitStagesCharacterComparisonStatement`, `SplitStagesCharacterIntegrand`, `SplitStagesComparison`, `SplitStagesRetraction`, `StructuralStatement`, `SurjectivityProof`, `SurjectivityStatement`.
- `Langlands.Representation.Jacquet`: `CharacterAveraging`, `Coinvariants`, `ExactProof`, `ExactStatement`, `Localization`, `LocalizationExactnessProof`, `LocalizationExactnessStatement`, `LocalizationTransport`, `PositiveCharacter`, `SmoothTwist`.
- `Langlands.Representation.MatrixCoefficient`: `Definitions`, `LawsProof`, `LawsStatement`.
- `Langlands.Representation.Mirabolic`: `LeftMixedProductSuccessor`, `MixedProducts`.
- `Langlands.Representation.Parabolic`: `GeometricPrerequisitesStatement`, `QuotientCompactProof`.
- `Langlands.Representation.RankinSelberg`: `GeneralLinearUnimodularity`, `LastRowCompactOrbitProof`, `LastRowCompactOrbitStatement`, `Measures`, `QuotientIntegrals`, `UnimodularityStatement`, `UnipotentUnimodularity`, `ZeroRowLastRowCutoffProof`, `ZeroRowLastRowCutoffStatement`.
- `Langlands.Representation.Smooth`: `Definitions`, `SmallRealizationProof`, `SmallRealizationStatement`.
- `Langlands.Representation.Smooth.Admissibility`: `CofinalProof`, `CofinalStatement`, `EquivalenceProof`, `EquivalenceStatement`.
- `Langlands.Representation.Smooth.Contragredient`: `CompactDualityProof`, `CompactDualityStatement`, `Definitions`, `FixedVectorsDefinitions`, `LawsProof`, `LawsStatement`.
- `Langlands.Representation.Smooth.FixedVectors`: `Definitions`.
- `Langlands.Representation.Smooth.SmoothPart`: `BasicProof`, `BasicStatement`, `Definitions`, `FixedVectorsDefinitions`.
- `Langlands.Representation.Smooth.Transfer`: `PullbackProof`, `PullbackStatement`, `SubquotientProof`, `SubquotientStatement`.
- `Langlands.Representation.Tensor`: `Finite`, `FiniteEquivalences`, `OneFactor`.
- `Langlands.Representation.Twist`: `AdmissibilityProof`, `AdmissibilityStatement`, `AlgebraProof`, `AlgebraStatement`, `ContinuousCharacterProof`, `ContinuousCharacterStatement`, `Definitions`, `RealPower`, `SmoothProof`, `SmoothStatement`, `SubquotientDefinitions`, `SubquotientProof`, `SubquotientStatement`.
- `Langlands.Representation.Unitary`: `Basic`.
- `Langlands.Representation.Whittaker`: `Algebraic`, `GeneralLinear`, `Iwasawa`.
- `Langlands.Topology`: `CompactNormCharacter`.
- `Langlands.Topology.CompactOpen`: `ConjugationStabilizer`, `NeighborhoodBasis`, `NeighborhoodBasisStatement`.
- `Langlands.Topology.Nonarchimedean`: `Subgroup`.

The 130 external boundary imports are listed next. This is the complete set
of non-project modules directly encountered while expanding the project
closure; Mathlib's internal import graph is supplied by the pinned prepared
environment and is not expanded by this inventory. These modules provide
ordinary algebra, categories, representations, topology, measures, local
fields and proof tactics, without project consumer conclusions.

- `Lean.Elab.Tactic`: `Omega`.
- `Mathlib.Algebra.BigOperators`: `Fin`, `Finprod`, `Pi`.
- `Mathlib.Algebra.BigOperators.Group.Finset`: `Basic`.
- `Mathlib.Algebra.CharP`: `Basic`.
- `Mathlib.Algebra.Group.Equiv`: `TypeTags`.
- `Mathlib.Algebra.Group.Hom`: `Instances`.
- `Mathlib.Algebra.Group.Subgroup`: `Ker`.
- `Mathlib.Algebra.Module`: `ULift`.
- `Mathlib.Algebra.Order.Archimedean`: `Basic`.
- `Mathlib.Algebra.Order.BigOperators.Group`: `Finset`.
- `Mathlib.Algebra.Polynomial`: `Lifts`.
- `Mathlib.Algebra.Ring`: `GeomSum`.
- `Mathlib.Analysis.Complex`: `Basic`, `Circle`.
- `Mathlib.Analysis.Fourier`: `FourierTransform`.
- `Mathlib.Analysis.InnerProductSpace`: `Defs`.
- `Mathlib.Analysis.Matrix`: `MeasurableSpace`.
- `Mathlib.Analysis.Normed.Module`: `FiniteDimension`.
- `Mathlib.Analysis.Normed.Unbundled`: `SpectralNorm`.
- `Mathlib.Analysis.Real`: `Sqrt`.
- `Mathlib.Analysis.SpecialFunctions.Complex`: `Circle`.
- `Mathlib.Analysis.SpecialFunctions.Pow`: `Complex`, `NNReal`, `Real`.
- `Mathlib.Basic.Complex`: `Basic`.
- `Mathlib.CategoryTheory`: `Skeletal`.
- `Mathlib.CategoryTheory.Abelian`: `Subcategory`.
- `Mathlib.CategoryTheory.Limits.ConcreteCategory`: `Basic`.
- `Mathlib.CategoryTheory.ObjectProperty`: `FullSubcategory`.
- `Mathlib.CategoryTheory.Pi`: `Basic`.
- `Mathlib.CategoryTheory.Products`: `Basic`.
- `Mathlib.Data.Fin`: `Rev`.
- `Mathlib.Data.Fin.Tuple`: `Basic`.
- `Mathlib.Data.Finset`: `NatAntidiagonal`.
- `Mathlib.Data.Fintype`: `Sum`.
- `Mathlib.Data.Int`: `LeastGreatest`.
- `Mathlib.Data.Matrix`: `Block`.
- `Mathlib.Data.Nat`: `Find`.
- `Mathlib.FieldTheory.Finite`: `Basic`.
- `Mathlib.GroupTheory`: `DoubleCoset`.
- `Mathlib.GroupTheory.Coset`: `Defs`.
- `Mathlib.GroupTheory.GroupAction`: `ConjAct`, `Quotient`.
- `Mathlib.GroupTheory.Subgroup`: `Centralizer`.
- `Mathlib.LinearAlgebra`: `Isomorphisms`.
- `Mathlib.LinearAlgebra.Dual`: `Lemmas`.
- `Mathlib.LinearAlgebra.Matrix`: `Block`, `Diagonal`, `Kronecker`, `Permutation`, `Reindex`, `Transvection`.
- `Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup`: `Basic`.
- `Mathlib.LinearAlgebra.PiTensorProduct`: `Basic`.
- `Mathlib.Logic.Equiv.Fin`: `Basic`.
- `Mathlib.MeasureTheory.Constructions`: `Pi`.
- `Mathlib.MeasureTheory.Function`: `LocallyIntegrable`, `SimpleFunc`.
- `Mathlib.MeasureTheory.Group`: `Integral`, `LIntegral`, `ModularCharacter`.
- `Mathlib.MeasureTheory.Integral`: `Marginal`, `Prod`.
- `Mathlib.MeasureTheory.Integral.Bochner`: `Basic`, `ContinuousLinearMap`, `Set`.
- `Mathlib.MeasureTheory.Integral.RieszMarkovKakutani`: `Real`.
- `Mathlib.MeasureTheory.Measure`: `Regular`.
- `Mathlib.MeasureTheory.Measure.Haar`: `Basic`, `DistribChar`, `MulEquivHaarChar`, `Unique`.
- `Mathlib.MeasureTheory.Measure.Typeclasses`: `Finite`.
- `Mathlib.NumberTheory.LocalField`: `Basic`.
- `Mathlib.NumberTheory.Padics`: `LocalField`, `RingHoms`.
- `Mathlib.Order`: `Atoms`.
- `Mathlib.RepresentationTheory`: `Basic`, `Coinduced`, `Coinvariants`, `Intertwining`, `Invariants`, `Irreducible`, `Subrepresentation`.
- `Mathlib.RepresentationTheory.Rep`: `Basic`, `Res`.
- `Mathlib.RingTheory`: `FiniteLength`.
- `Mathlib.RingTheory.DedekindDomain`: `IntegralClosure`.
- `Mathlib.RingTheory.Finiteness`: `Basic`.
- `Mathlib.RingTheory.Ideal.Quotient`: `Operations`.
- `Mathlib.RingTheory.Noetherian`: `Basic`, `Defs`.
- `Mathlib.RingTheory.RamificationInertia`: `Basic`.
- `Mathlib.RingTheory.SimpleModule`: `Basic`.
- `Mathlib.RingTheory.Valuation`: `Integral`.
- `Mathlib.Tactic`: `Linarith`, `NoncommRing`.
- `Mathlib.Topology`: `Bases`, `LocallyClosed`, `UrysohnsLemma`.
- `Mathlib.Topology.Algebra`: `ContinuousMonoidHom`, `MulAction`, `OpenSubgroup`, `Support`.
- `Mathlib.Topology.Algebra.Group`: `Basic`, `Matrix`, `OpenMapping`, `Pointwise`, `Quotient`, `Subgroup`, `Units`.
- `Mathlib.Topology.Algebra.Module`: `FiniteDimension`.
- `Mathlib.Topology.Algebra.Nonarchimedean`: `Basic`.
- `Mathlib.Topology.Algebra.ProperAction`: `Basic`.
- `Mathlib.Topology.Algebra.Ring`: `Compact`.
- `Mathlib.Topology.Algebra.ValuativeRel`: `ValuativeTopology`.
- `Mathlib.Topology.Algebra.Valued`: `NormedValued`.
- `Mathlib.Topology.Baire`: `LocallyCompactRegular`.
- `Mathlib.Topology.Compactness`: `Compact`, `LocallyCompact`, `SigmaCompact`.
- `Mathlib.Topology.Connected`: `TotallyDisconnected`.
- `Mathlib.Topology.ContinuousMap`: `CompactlySupported`.
- `Mathlib.Topology.Homeomorph`: `Lemmas`, `Quotient`.
- `Mathlib.Topology.Instances.NNReal`: `Lemmas`.
- `Mathlib.Topology.LocallyConstant`: `Basic`.
- `Mathlib.Topology.Order`: `Compact`.

The complete project Lean-code scan found no excluded declaration
and no proof holes, added axioms or prohibited execution syntax.
The broader name scan was reconciled with the actual bodies: its extra
hits are finite-length predicates, elementary supercuspidal-definition and
contragredient infrastructure, matrix upper-head notation, compact-character
relation detection, and the independent mirabolic derivative-detection
import discussed above. This scan supplements the mathematical dependency
trace and does not replace it.

The final declaration recompiles with universe parameters `uF,uV`
and only the kernel assumptions `propext`, `Classical.choice` and
`Quot.sound`.
