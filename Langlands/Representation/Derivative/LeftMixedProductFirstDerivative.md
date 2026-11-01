# The first derivative of a left mixed product

The internal definition
`Langlands.Derivative.leftMixedProductFirstDerivativeIso` constructs the
order-one instance of the natural isomorphism in BZ77 Corollary 4.14(a), for
all GL ranks, including an arbitrary representation of GL₀. It is an ingredient
for `LeftMixedProductDerivativeIso`, not a proof of that entire proposition:
orders greater than one and `LeftMixedProductDerivativeVanishing` remain separate
obligations. Its type is data, an actual natural isomorphism of the published
functors, rather than a proposition postulating that data.

## Exact scope and construction

Fix arbitrary `{p : ℕ}`, `[Fact p.Prime]`, `F : PadicField.{uF} p`, the supplied
`T : F.TopologicalData`, a unitary additive character `ψ`, and `k r : ℕ`.
The field universe `uF` and input-carrier universe `uV` are independent. After
installing `T.topology`, the definition has type

```text
T.leftMixedProductFunctor k r ⋙
    mirabolicDerivativeOfOrder T ψ (k+r) 1 ⟨0<1, 1≤k+r+1⟩ ⋙
      generalLinearRankCast T (k+r+1-1 = k+(r+1-1))
  ≅ (𝟭 _).prod (mirabolicDerivativeOfOrder T ψ r 1 ⟨0<1, 1≤r+1⟩) ⋙
      T.binaryNormalizedProductFunctor k (r+1-1).
```

Both inequalities and the displayed rank equality are proved by natural-number
arithmetic. The source is the product category of actual smooth representations
of GLₖ and `mirabolic r = P_(r+1)`. The target is the actual smooth category of
GL_(k+(r+1-1)), at carrier universe `max uF uV`. Thus the source derivative is
indexed by `k+r`, with its published rank cast retained in the definition's
signature. This covers `r=0`, where the second derivative takes P₁ to GL₀.
There is no P₀. Neither GL₀ input nor GL₀ output is identified with a unit object
or a one-dimensional vector space.

The proof splits only on `k`.

* For `k=0` it applies the independently published
  `LeftMixedProductZeroRank.leftMixedProductZeroRankIso T ψ r 1` directly. That
  comparison already has the exact source derivative and target cast, so no
  objectwise replacement or additional rank identification is needed here.
* For `k=k'+1` it simplifies the goal using only
  `mirabolicDerivativeOfOrder_one`, `generalLinearRankCast_refl`, and
  `Functor.comp_id`. In order one, the published derivative is exactly Psi-minus;
  `r+1-1=r` and the target cast is reflexive. The resulting goal is the natural
  isomorphism asserted by the independently published theorem
  `MirabolicProductMinus.leftPsiCompatibility.{uF,uV} T k' r`.
  `Classical.choice` extracts its isomorphism from `Nonempty`.

In positive rank, `Classical.choice` selects a natural isomorphism whose
existence is established by the published Psi comparison. Its components,
inverses and naturality laws are those of the selected functor isomorphism,
transported by the displayed functor equalities. The `Nonempty` proposition
does not specify that these selected components equal the explicit witness
used in its existence proof.

For provenance, that published existence proof constructs a witness by composing
the radical-coinvariant/compact-induction comparison with the normalized
binary-induction comparison. The former descends the tensor quotient; the latter
transports the coefficient pointwise and uses compactness of the actual
parabolic quotient. For `r=0`, its witness instead uses evaluation from the
whole section subgroup and the binary right-zero tensor equivalence. These
formulas describe the witnesses in the imported proof, without identifying them
with this definition's choice. All determinant factors and the inverse-half
minus normalization remain those of the published functors.

For `k=0`, the imported comparison first evaluates induction from the whole group
at 1 and sends `a ⊗ b` to `b ⊗ ULift.up a`. It commutes the order-one localization,
pullback and twist past this inert GL₀ factor by `[b ⊗ a] ↦ [b] ⊗ a`, uses the
entry-preserving reindex corresponding to the rank equality, and applies the
inverse binary-left-zero tensor comparison. Its inverse reverses these steps.
Only GL₀ group elements are subsingleton; the entire carrier of `A` is retained.

Both imported comparisons are natural in every pair morphism `(f₁,f₂)` at once.
The quotient and tensor maps commute with both input maps, and evaluation and
rank reindex do so as well. The equality rewrites above preserve complete functor
isomorphisms. Consequently this definition supplies naturality in both inputs,
not merely equivariant objectwise equivalences. It adds no admissibility,
irreducibility, finite length, finite dimension, genericity, nonzero-object,
character, or theorem-valued hypothesis.

## Original and internal provenance

I. N. Bernstein and A. V. Zelevinsky, *Induced representations of reductive
p-adic groups I*, Ann. Sci. ENS (4) 10 (1977), 441–472, registered source
`bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`, states
Corollary 4.14(a) on printed p.458 (one-based PDF p.19), following the mixed
products of §4.12(II), printed p.457 (PDF p.18), and Proposition 4.13(b).
The order convention comes from §§3.2–3.5, printed pp.450–452 (PDF pp.11–13).
The original also discusses the proof of 4.13(b) in §7.2, printed p.471
(PDF p.32). These original passages and page images were read for the task;
a bounded project/literature errata search found no applicable BZ77 entry.

This module is a derived internal case assembly. Its positive-rank input is the
published proof of the left Psi clause of 4.13(b), rather than the citation as
an assumed theorem. The arbitrary-carrier GL₀ argument is internal: the source
does not separately give that comparison and uses its convention P₀=0.
`ZeroRankTensor` proves the localization/tensor fact directly by quotient
universal properties, in agreement with BZ77 Proposition 1.9(g), printed p.445
(PDF p.6). This module assumes no unproved source assertion.

The direct imported inputs were checked as independently accepted and published:

| Published Lean input | Verified role |
| --- | --- |
| `MirabolicProductMinus.leftPsiCompatibility` in `MirabolicProductMinusLeftPsi` | Exact left Psi proposition, Reviewer 6250, no qualifications; published at `5c739daf70eeb88f11ce9139aeb3ed04904874ca`. |
| `LeftMixedProductZeroRank.leftMixedProductZeroRankIso` | All-order arbitrary-carrier GL₀ natural comparison, specialized here to order one; Reviewer 6175, no qualifications; published at `2003a7a6a41b5e54c3f790e0887743ed616ed614`. |
| `ZeroRankTensor` constructions used by the preceding comparison | Direct quotient/tensor, pullback, twist and cast commutations; replacement reviewed by Reviewer 6107 without qualifications and published at `9a8ca758097242bde4147f33304f43fceef22fa4`. |

The Psi proof's two direct construction inputs, `MirabolicProductMinusLeftPsiInduction`
and `Induction.BinaryPositiveCompact`, were independently reviewed by Reviewers
6173 and 6043 and published at `2003a7a6a41b5e54c3f790e0887743ed616ed614` and
`9a8ca758097242bde4147f33304f43fceef22fa4`, respectively. Publication and semantic
review were verified separately from local compilation. Published mathematics is
imported by Lean name; no artifact identity occurs in the Lean mathematics.

## Actual mathematical dependency audit

The audit below applies to both complete exclusion sets of task
`7e19f753-4515-4d87-9256-f366b6fc5683` revision 1, including their direct and
transitive proof dependencies, mathematical conclusions, proof successors and
downstream consequences. It checks the shared lower constructions as well as
this short case assembly. The complete source import closure is listed below.
All 354 imported Lean/Markdown files match Library commit
`3556873fa475ebf7c4932f5d037eb3dea71c4ddb` byte for byte. The target pair and its
dependency closure are unchanged.

| Actual input or potentially broad import | Body checked and mathematical scope |
| --- | --- |
| New case assembly | Only the two published comparisons, order-one derivative identity, reflexive cast law, functor identity law and arithmetic are used. No higher-order compatibility or vanishing input occurs. |
| Psi induction comparison | The actual radical projection, surjectivity, kernel, subgroup, topology and smoothness conditions are proved in the published helper. The ordinary normal-coinvariant comparison, split quotient and character twist identify the actual localized compact induction. |
| Normal-coinvariant and split lower proofs | Relation-kernel arguments, compact induction surjectivity, local sections, cutoff and compact averaging prove the lower maps and bijectivity. None uses representation finiteness or a derivative consumer. |
| Determinant normalization | The Psi helper proves the determinant factorization and real-power identity. Its assembly retains both blocks and identifies the entire coefficient scalar with the binary parabolic half modulus. No normalization comparison is left as a premise. |
| Positive binary compact comparison | Pointwise coefficient transport, binary tensor action/map laws and compact-inclusion bijectivity identify the actual binary product. Parabolic quotient compactness follows from `G=P K` and compactness of the integral subgroup. The Iwasawa input is proved by elementary column reduction. |
| `MirabolicProductRestrictionFactors` | The binary helper uses only `FiniteTensor.binaryLinearEquiv`, its external action law and external-map law. Neither a restriction sequence nor a geometric-lemma conclusion is an input. |
| `SplitStagesComparison` | Only `Induction.compactInducedEquiv`, pointwise transport by a coefficient equivalence, is used by the binary helper. The larger stages/integral import closure is included below; it introduces no consumer or finiteness assumption. |
| GL₀ comparison | Whole-group evaluation, the trivial inducing character, swap/lift, entry-preserving reindex and binary-left-zero tensor equivalence construct the comparison. The GL₀ action is trivial because its group is subsingleton, without collapsing its carrier. |
| `ZeroRankTensor` | The forward and backward quotient maps `[v ⊗ a] ↔ [v] ⊗ a` are constructed and proved inverse on generators. Equivariance, naturality, restriction, twists and rank casts are proved directly; iteration uses associators and whiskering. No derivative consumer supplies tensor commutation. |
| `Mirabolic.MixedProducts` and `Induction.BinaryProduct` | Actual subgroup, inducing coefficient, normalized compact/smooth induction, zero-rank tensor models and actual functor maps are used unchanged. Their lower inputs are group matrices, smoothness, tensor algebra and induction definitions, not classification. |
| `Derivative.Homogeneity` | This module's name is not a Ze80 homogeneity input. Its body supplies `mirabolicDerivativeOfOrder`, rank casts, elementary zero-carrier facts and homogeneity predicates; the only proved homogeneity facts there concern subsingleton carriers. No Ze80 5.3 or 6.2 theorem occurs. |
| Whittaker/Rankin–Selberg imports | Lower character, matrix-coefficient, measure, compact-orbit, cutoff and unimodularity constructions occur. Iwasawa is the elementary group decomposition above. They contain none of the excluded coinvariant-finiteness or classification conclusions. |
| `Category.Basic` and `Filtration.Definitions` | The former defines finite length using Mathlib and the latter defines filtrations. No mirabolic finite-length theorem, consumer finiteness route or Leibniz filtration supplies a proof input. |
| Compatibility statement module | It supplies the unchanged proposition types and functor definitions. The only clause used as a theorem is the independently published left Psi proof. A Prop definition, draft, conditional result or pending proof supplies no proved input. |

## First complete exclusion set: inherited Ze80 6.2 route

Each row rules out both the named conclusions and their successors and transitive
consequences. The reasons refer to the actual construction audit above, not just
to absence of a task identifier. Repeated conditions inherited through more than
one consumer retain their full scope.

| Excluded condition and task | Audit result |
| --- | --- |
| Ordered-socle existence / `OrderedMultisegmentSocleExistence`, `23189526-80b0-4828-a6d4-7ebec2cbeef5`; socle exhaustion / `MultisegmentSocleExhaustion`, `f3a69bc8-7312-4f82-8a7d-ea3c8188cb63` | No socle, essential-subobject or ordered-existence input; components come from quotient and induction equivalences. |
| Analytic segment classification, `aca8805b-054f-4d56-8045-12db7f623404` | No segment or analytic classification input. |
| Unlinked segment-socle product irreducibility, `23e98d90-6055-4e35-91a9-b0f5d8a84961` | No irreducibility argument or product criterion is used. |
| Final `SegmentSocleProductIrreducibility`, `2ae5cbe5-0701-4509-88a0-db8cbeb35be4` | No criterion or consequence supplies an input. |
| `AdjacentUnlinkedSegmentSocleSwap`, adjacent commutation `e3634665-571b-4852-9f4c-bab8a1053434`, and `TwoSegmentSocleCommutation` | No socle-product swap or commutation theorem; the tensor swap in GL₀ is elementary linear algebra. |
| Special-head product criterion / `SegmentHeadProductIrreducibility`, `8364e73f-14ec-4d14-8f2b-1555a7c1ce95` | No head or special-head criterion is used. |
| Special-head multisegment exhaustion, `3bfb61fa-1129-4fc9-83fd-7fcfec22106e` | No exhaustion input. |
| Ordered special/strong-head existence, `ebea9a8a-9b21-4208-aa31-98c2dea1f8a3` | No head-existence input. |
| Quotient coverage, `20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584` | No representation-coverage theorem; quotient universal properties here are elementary module operations. |
| Tempered block uniqueness, `52e97845-36bb-457d-b76f-70753334b88c` | No tempered decomposition or uniqueness input. |
| `SquareIntegrableLanglandsClassification`, `1cb45da2-7007-4351-a694-594fb148b8d1` | No square-integrable or Langlands classification input. |
| Square-integrable exhaustion, `cd8ab97c-0b78-4bce-97c4-d307a28159a4`; regular exhaustion, `bf433f0a-921a-428c-b0c0-6475438125ac` | Neither exhaustion result nor a consequence is used. |
| `GenericSegmentProductUniqueness`, `30341ae4-65f2-4a0e-9283-763db01a409e` | No genericity or segment uniqueness input. |
| Ordered special-segment conversion, `8252833d-c269-41a9-824c-5879e531b23b` | No head/socle conversion input. |
| Forward special essential square-integrability / `SegmentSpecialEssentialSquareIntegrability`, `5eece9e8-7f6b-4ea9-abea-a1f9f1b8c807` | No square-integrability input. |
| Individual special-head/reverse-socle existence, `67279e36-f3c2-42e3-9302-11729784042e` | No individual segment-existence input. |
| Individual segment-socle/reverse-head existence, `4ca79bbd-589e-476b-9f65-661e799984b5` | No individual segment-existence input. |
| `SegmentFullJacquetFormula`, statement/arrangement `ed48ae06-964c-4c84-9e62-978f5a953ca7` and its exact proof successor | No segment Jacquet formula; the localized coefficient computation is general and proved directly. |
| `SegmentHeadJacquetFormula`, `55ad1e10-62d8-46b7-a081-909ef0056426` | No segment head Jacquet input. |
| `SegmentSocleJacquetFormula`, `b95105c6-f8bb-4641-ae53-2f49d1e7f034` | No segment socle Jacquet input. |
| `SegmentSpecialJacquetExponentNormFormula`, `92aea10f-62ac-4e0b-bd4a-9a80909797c5` | No segment exponent formula; determinant factors are computed from matrices and characters. |
| Combined Ze80 §5.4 reduction and strong-indecomposability conclusion, including its consumer `ff4738d8-47e3-433b-bedc-629bc2d492a7` | No detection, indecomposability or combined reduction input. |
| `TwoSupercuspidalNonadjacentProductIrreducible`, `3c9849a4-a6c0-43ac-9982-d15ed76bf1e9`; `TwoSupercuspidalProductStructure`, `ab61f565-1427-4746-ba77-46097563e962`, including adjacent composition/Jacquet conjuncts | No supercuspidal or two-factor structure theorem. |
| Ze80 §3.5 and §9.6 segment derivatives; segment-socle portion of `8e5b4563-0365-41c7-b134-70f2a0b36292` | No segment derivative formula or either portion of that task is used. The order-one identity is definitional; Psi and GL₀ inputs are published proofs. |
| Ze80 4.2 or 9.7 product criteria, Ze80 9.3 analytic/square-integrability results, and any classification/exhaustion theorem | None is used. No linked-pair converse is used circularly to establish Proposition 1.11. |
| Consumer homogeneity: Ze80 6.2 `b711af72-fdf9-4b32-a450-937911426822`, Ze80 5.3 `49d8eea3-1f52-4505-bfce-d76bf8ed5b8a` and its proof `6bb62ea4-c7e1-4325-9eb6-b8bbee1f65c4` | No consumer homogeneity theorem or proof dependency. `RestrictedProductLevel`, `SegmentSocleProductHomogeneityInduction` and `SegmentSocleProductCaseTwo` are absent from the closure. |
| All-rank GL Leibniz consumer `3238f371-e9a2-42ce-8b5d-9c4d3400ff55` | No Leibniz theorem, filtration proof or downstream consequence is used. |
| Operator-paused minus exactness, `b65bc667-6951-4bd5-82af-10fb7046df7f` | No input from that task, no duplicate replacement, no request for resumption, and no contact with Worker 127. |

## Second complete exclusion set: shared all-rank Leibniz upstream scope

All conditions in the preceding table also hold for the second inherited set:
in particular its repeated classification, exhaustion, two-supercuspidal,
individual existence, segment Jacquet and analytic restrictions are checked by
those same rows without weakening. The following rows cover the additional
named conclusions and proof-successor IDs of the shared upstream scope and its
binding exact-derivative contract `2e5183b1-01e9-44fb-b26c-f4521a25c7c7` revision 2.

| Additional or more explicitly named condition | Audit result |
| --- | --- |
| `UnlinkedSegmentSocleProductIrreducible`, `LinkedSegmentSocleReverseProductStructure`, `LinkedSegmentSoclePairReducible`; `23e98d90-6055-4e35-91a9-b0f5d8a84961`, `a55c4267-7e3a-43f6-8bb1-ce319e1d0aa9`, `8fa9f68b-fa1b-431a-97f6-5b163964d1fc` | None is an input. The induction/coinvariant equivalences are constructed before any segment or irreducibility argument. |
| `JuxtaposedSegmentSocleReverseProductStructure`, `LinkedSegmentSocleReverseProductQuotientHom`; `7ff2a1e9-89dc-439e-a861-a567b3db92bf` and successors | No segment quotient-homomorphism or juxtaposed-product input. |
| Adjacent socle commutation successor `cded83f3-df9c-4018-bc61-dc54f5c1f9ab` | Absent together with its parent commutation result. |
| `TwoSegmentSocleCommutation`, `426911b4-6620-413f-8065-04b25287f3bd`, `66e3b87c-647e-41e4-af18-df4d436765f0` | No commutation result or successor. The GL₀ tensor swap uses tensor algebra only. |
| `LinkedSegmentSocleGluing`, `c84cd52c-3ff3-4024-be50-8b84dd480888`, `6780b79c-9526-46aa-b8b4-00377d68b1ea` | No gluing or extension classification input. |
| Parent six-statement contribution's (b), (d), (e), (f), every segment derivative, existence, Jacquet or classification conclusion, and proofs depending on them | None is used. No cuspidal or segment derivative theorem supplies the tensor or localization maps. |
| `Langlands.Whittaker.SupercuspidalCoinvariantFinitenessStatement`, all-character single-block task `62de5903-b616-4b5c-88eb-a066b77c5467`, successors and consequences | No supercuspidal/all-character finiteness input; compact averaging in induction is a direct local construction. |
| `Langlands.Whittaker.IrreducibleCoinvariantFinitenessStatement`, parent `5ab445dc-d2b4-4072-80d1-6370870a4a26` | No irreducible Whittaker-finiteness input or downstream consequence. |
| `LeviCuspidalCoinvariantFinitenessStatement`, proof `3ff5c8fb-397c-4345-bcb3-5d98a0993d18` | No Levi/cuspidal finiteness input or downstream consequence. |
| Mirabolic finite-length route `5428fe2c-013c-482d-aa6e-7df43e7191aa` using the prohibited finiteness | No mirabolic finite-length proof or pending repair is used. The categorical finite-length definition in `Category.Basic` proves none of these assertions. |
| General derivative/tensor results must not be supplied by their consumers | Psi and GL₀ comparisons are independently published constructions; tensor commutation is proved by quotient maps. No consumer assumption fills a missing proof. |
| Shared character, Jacquet, top-localization, exactness, geometric lemma, cuspidal-support and finite-length infrastructure requires an independence check | The actual character/localization/induction bodies are covered by the preceding audit. No top-localization consumer, general exactness, geometric-lemma, cuspidal-support or finite-length theorem is needed. |
| Ownership and run controls | Ownership pointers grant no hypothesis. The separate 4.13(b,c), 4.13(d), 4.14(b) and Whittaker-finiteness tasks are not duplicated; no suspended collaborator or paused worker is awakened. |

A code scan of all 178 project modules including this root checked all 63 UUIDs
appearing in the contract's objective/context, the named excluded declarations,
and broader segment/socle/head/classification/finiteness families. The only
exact-name hits were the permitted compatibility-statement import and imports
of `Derivative.Homogeneity`. Broader hits were the elementary homogeneity
predicates/zero-carrier lemmas described above and the `HasFiniteLength`
definition/Mathlib import in `Category.Basic`. No excluded consumer declaration,
proof hole, invented axiom or forbidden execution construct was found. This scan
supports, rather than replaces, the mathematical body and provenance audit above.
Declaration inspection of the definition confirms independent `uF,uV` and only
`propext`, `Classical.choice`, `Quot.sound` as axioms. Compilation is development
evidence; this new definition still requires its own independent review.

## Complete transitive project import closure

The two direct imports are `Derivative.MirabolicProductMinusLeftPsi` and
`Derivative.LeftMixedProductZeroRank`, with the full prefix `Langlands.Representation`.
The list below contains every transitive project import, excluding this root:
177 modules. Mathlib is supplied by the pinned environment. The Psi closure
accounts for 175 modules; the only additions are `LeftMixedProductZeroRank` and
`ZeroRankTensor`, whose actual constructions are audited above.

```text
Langlands.Analysis.Local.ModularCompactAverage
Langlands.Analysis.Local.QuotientAutomorphismProof
Langlands.Analysis.Local.QuotientAutomorphismStatement
Langlands.Analysis.Local.QuotientAverageReal
Langlands.Analysis.Local.QuotientMass
Langlands.Analysis.Local.QuotientMeasure
Langlands.Analysis.Local.QuotientMeasurePrerequisites
Langlands.Analysis.Local.QuotientPositiveLifting
Langlands.Analysis.Local.QuotientTopology
Langlands.Analysis.Local.SplitKernelQuotient
Langlands.Group.GL.Basic
Langlands.Group.GL.BlockModulus
Langlands.Group.GL.Blocks
Langlands.Group.GL.CompactOpen
Langlands.Group.GL.Maps
Langlands.Group.GL.Mirabolic
Langlands.Group.GL.MirabolicMixedProductSubgroups
Langlands.Group.GL.MirabolicModularCharacterProof
Langlands.Group.GL.MirabolicModularCharacterStatement
Langlands.Group.GL.MirabolicModulusProof
Langlands.Group.GL.MirabolicModulusStatement
Langlands.Group.GL.MirabolicOppositeIntersection
Langlands.Group.GL.MirabolicProjection
Langlands.Group.GL.MirabolicRadical
Langlands.Group.GL.Nonarchimedean
Langlands.Group.GL.NonarchimedeanStatement
Langlands.Group.GL.NormalizedCharacter
Langlands.Group.GL.OppositeBlocks
Langlands.Group.GL.Padic
Langlands.Group.GL.PadicBlocks
Langlands.Group.GL.PadicOppositeBlocks
Langlands.Group.GL.PadicUpperUnipotent
Langlands.Group.GL.RankMaps
Langlands.Group.GL.RankReindex
Langlands.Group.GL.ReverseBlocks
Langlands.Group.GL.TriangularParabolic
Langlands.Group.GL.UpperUnipotent
Langlands.Group.HaarModulus
Langlands.HarmonicAnalysis.AlgebraicIntegral
Langlands.HarmonicAnalysis.AlgebraicIntegrand
Langlands.HarmonicAnalysis.Basic
Langlands.HarmonicAnalysis.Conductor
Langlands.HarmonicAnalysis.PadicAdditiveConductorProof
Langlands.HarmonicAnalysis.PadicHaarScalingStatement
Langlands.HarmonicAnalysis.PadicLatticeTopology
Langlands.HarmonicAnalysis.PadicRectangularHaarScalingProof
Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof
Langlands.LocalFactor.Harmonic.Statement
Langlands.LocalField.Canonical
Langlands.LocalField.Definitions
Langlands.LocalField.Normalization.Definitions
Langlands.LocalField.Normalization.Proof
Langlands.LocalField.Normalization.Statement
Langlands.LocalField.Topology
Langlands.Representation.Category.Basic
Langlands.Representation.Category.Subquotients
Langlands.Representation.Category.Twist
Langlands.Representation.Compact.Definitions
Langlands.Representation.Compact.FiniteMean
Langlands.Representation.Compact.OrbitMeanTranslation
Langlands.Representation.Compact.ProjectionProof
Langlands.Representation.Compact.ProjectionStatement
Langlands.Representation.Compact.SurjectivityProof
Langlands.Representation.Compact.SurjectivityStatement
Langlands.Representation.Conductor.Congruence
Langlands.Representation.Derivative.Homogeneity
Langlands.Representation.Derivative.Iteration
Langlands.Representation.Derivative.LeftMixedProductZeroRank
Langlands.Representation.Derivative.MinusVanishing
Langlands.Representation.Derivative.MirabolicCharacter
Langlands.Representation.Derivative.MirabolicLatticeBox
Langlands.Representation.Derivative.MirabolicMinus
Langlands.Representation.Derivative.MirabolicProductMinusCompatibilityStatement
Langlands.Representation.Derivative.MirabolicProductMinusLeftPsi
Langlands.Representation.Derivative.MirabolicProductMinusLeftPsiInduction
Langlands.Representation.Derivative.MirabolicProductRestrictionFactors
Langlands.Representation.Derivative.MirabolicProductRestrictionOrbits
Langlands.Representation.Derivative.ZeroRankTensor
Langlands.Representation.Dual.Definitions
Langlands.Representation.Filtration.Definitions
Langlands.Representation.Geometric.ClosedSubgroupDefinitions
Langlands.Representation.Induction.BinaryPositiveCompact
Langlands.Representation.Induction.BinaryProduct
Langlands.Representation.Induction.BlockFactors
Langlands.Representation.Induction.CharacterTwistProof
Langlands.Representation.Induction.CompactAutomorphism
Langlands.Representation.Induction.CompactAutomorphismIntegralProof
Langlands.Representation.Induction.CompactAutomorphismIntegralStatement
Langlands.Representation.Induction.CompactCoinvariantBijectivityProof
Langlands.Representation.Induction.CompactCoinvariantBijectivityStatement
Langlands.Representation.Induction.CompactCoinvariantIntegral
Langlands.Representation.Induction.CompactCoinvariantLocalInverseProof
Langlands.Representation.Induction.CompactCoinvariantLocalInverseStatement
Langlands.Representation.Induction.CompactLocalSection
Langlands.Representation.Induction.CompactLocalSectionSpanningProof
Langlands.Representation.Induction.CompactLocalSectionSpanningStatement
Langlands.Representation.Induction.CompactLocallyConstant
Langlands.Representation.Induction.CompactQuotientCutoff
Langlands.Representation.Induction.CompactQuotientProof
Langlands.Representation.Induction.CompactSurjectivityProof
Langlands.Representation.Induction.CompactSurjectivityStatement
Langlands.Representation.Induction.CompactTransitivityProof
Langlands.Representation.Induction.CompactTransitivityStatement
Langlands.Representation.Induction.Definitions
Langlands.Representation.Induction.InverseTranspose
Langlands.Representation.Induction.NormalCoinvariantKernelProof
Langlands.Representation.Induction.NormalCoinvariantKernelStatement
Langlands.Representation.Induction.NormalCoinvariantMap
Langlands.Representation.Induction.NormalCoinvariantProof
Langlands.Representation.Induction.NormalCoinvariantStatement
Langlands.Representation.Induction.NormalSplitComparison
Langlands.Representation.Induction.OppositeParabolic
Langlands.Representation.Induction.Parabolic
Langlands.Representation.Induction.SplitKernelCompact
Langlands.Representation.Induction.SplitKernelCovariance
Langlands.Representation.Induction.SplitKernelEquivariant
Langlands.Representation.Induction.SplitKernelIntegral
Langlands.Representation.Induction.SplitQuotientProof
Langlands.Representation.Induction.SplitQuotientStatement
Langlands.Representation.Induction.SplitStagesComparison
Langlands.Representation.Induction.SplitStagesRetraction
Langlands.Representation.Induction.StructuralStatement
Langlands.Representation.Induction.SurjectivityProof
Langlands.Representation.Induction.SurjectivityStatement
Langlands.Representation.Jacquet.CharacterAveraging
Langlands.Representation.Jacquet.Coinvariants
Langlands.Representation.Jacquet.Localization
Langlands.Representation.Jacquet.PositiveCharacter
Langlands.Representation.Jacquet.SmoothTwist
Langlands.Representation.MatrixCoefficient.Definitions
Langlands.Representation.MatrixCoefficient.LawsProof
Langlands.Representation.MatrixCoefficient.LawsStatement
Langlands.Representation.Mirabolic.MixedProducts
Langlands.Representation.Parabolic.GeometricPrerequisitesStatement
Langlands.Representation.Parabolic.QuotientCompactProof
Langlands.Representation.RankinSelberg.GeneralLinearUnimodularity
Langlands.Representation.RankinSelberg.LastRowCompactOrbitProof
Langlands.Representation.RankinSelberg.LastRowCompactOrbitStatement
Langlands.Representation.RankinSelberg.Measures
Langlands.Representation.RankinSelberg.QuotientIntegrals
Langlands.Representation.RankinSelberg.UnimodularityStatement
Langlands.Representation.RankinSelberg.ZeroRowLastRowCutoffProof
Langlands.Representation.RankinSelberg.ZeroRowLastRowCutoffStatement
Langlands.Representation.Smooth.Admissibility.CofinalProof
Langlands.Representation.Smooth.Admissibility.CofinalStatement
Langlands.Representation.Smooth.Definitions
Langlands.Representation.Smooth.SmoothPart.BasicProof
Langlands.Representation.Smooth.SmoothPart.BasicStatement
Langlands.Representation.Smooth.SmoothPart.Definitions
Langlands.Representation.Smooth.Transfer.PullbackProof
Langlands.Representation.Smooth.Transfer.PullbackStatement
Langlands.Representation.Smooth.Transfer.SubquotientProof
Langlands.Representation.Smooth.Transfer.SubquotientStatement
Langlands.Representation.Tensor.Finite
Langlands.Representation.Tensor.FiniteEquivalences
Langlands.Representation.Tensor.OneFactor
Langlands.Representation.Twist.AdmissibilityProof
Langlands.Representation.Twist.AdmissibilityStatement
Langlands.Representation.Twist.AlgebraProof
Langlands.Representation.Twist.AlgebraStatement
Langlands.Representation.Twist.ContinuousCharacterProof
Langlands.Representation.Twist.ContinuousCharacterStatement
Langlands.Representation.Twist.Definitions
Langlands.Representation.Twist.RealPower
Langlands.Representation.Twist.SmoothProof
Langlands.Representation.Twist.SmoothStatement
Langlands.Representation.Twist.SubquotientDefinitions
Langlands.Representation.Twist.SubquotientProof
Langlands.Representation.Twist.SubquotientStatement
Langlands.Representation.Whittaker.Algebraic
Langlands.Representation.Whittaker.GeneralLinear
Langlands.Representation.Whittaker.Iwasawa
Langlands.Topology.CompactNormCharacter
Langlands.Topology.CompactOpen.ConjugationStabilizer
Langlands.Topology.CompactOpen.NeighborhoodBasis
Langlands.Topology.CompactOpen.NeighborhoodBasisStatement
Langlands.Topology.Nonarchimedean.Subgroup
```
