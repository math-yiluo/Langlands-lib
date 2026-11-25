# Derivatives of left mixed products in every GL rank

The theorem `Langlands.Derivative.leftMixedProductDerivative` proves the
entire published proposition
`Langlands.Derivative.LeftMixedProductDerivative.{uF,uV} F T`.
Its outer telescope is exactly
`{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)`.
There is no additional premise. The two universes are independent.

The projection theorems `leftMixedProductDerivativeIso F T` and
`leftMixedProductDerivativeVanishing F T` expose the two conjuncts.
The first gives actual natural isomorphisms for every unitary additive
character, every GL rank `k`, every mirabolic index `r`, and every order
`1 ≤ i ≤ r + 1`. The second gives subsingleton carriers for every
`r + 1 < i ≤ k + r + 1`. The supplied topology, actual determinant-normalized
minus functors, mixed and binary products, characters, whole carriers and
rank transports are unchanged.

## Exact functors and boundary cases

The Library convention is `mirabolic r = P_(r+1)`. For
`hi : 0 < i ∧ i ≤ r + 1`, the first conjunct asserts

```text
T.leftMixedProductFunctor k r ⋙
    mirabolicDerivativeOfOrder T ψ (k+r) i ⟨hi.1, _⟩ ⋙
      generalLinearRankCast T (k+r+1-i = k+(r+1-i))
  ≅ (𝟭 _).prod (mirabolicDerivativeOfOrder T ψ r i hi) ⋙
      T.binaryNormalizedProductFunctor k (r+1-i).
```

The domain is the full product category of smooth representations of
`GL_k` and `P_(r+1)` with input-carrier universe `uV`; the target has
carrier universe `max uF uV`. Every pair morphism is included.
In particular `r=0`, `i=1`, `i=r+1`, arbitrary GL₀ input carriers and
GL₀ derivative outputs are covered. There is no P₀ object in this
implementation. For the vanishing conjunct, the top valid order
`i=k+r+1` is included. When `k=0` its high-order range is empty.
No admissibility, irreducibility, finite dimension, finite length,
genericity, nonzero-object or theorem-valued premise is imposed.

## Implemented proof

The final theorem pairs the two helper conclusions and supplies
`MirabolicProductMinus.leftPhiCompatibility T` to each explicit Phi
argument. That exact clause has a published
proof. The helper modules are ported together with this module and are explained
in [LeftMixedProductHigher](LeftMixedProductHigher.md) and
[LeftMixedProductVanishing](LeftMixedProductVanishing.md).

For positive GL rank `k+1`, the isomorphism helper inducts on the number
`j=i-1` of Phi steps while fixing the second derivative's target rank `n`.
At `j=0`, `mirabolicDerivative_zero` gives Psi-minus and the published
`MirabolicProductMinus.leftPsiCompatibility` gives the full natural
comparison. At `j+1`, `mirabolicDerivative_succ` applies the largest-rank
Phi first. The published Phi comparison moves that step to the second
input, and whiskering the induction hypothesis handles the remaining
derivative. Product-functor composition, associators and unitors combine
these maps into a natural isomorphism.

The rank bookkeeping is explicit. `leftPhiStepIso` postcomposes the
published clause with the inverse cast
`(k+1)+r = k+(r+1)`; `phiMinus_rankCast` moves the source cast past Phi,
and `mirabolicRankCast_trans` and `mirabolicRankCast_symm_comp` combine
or cancel actual equality transports. The target-rank induction uses
`(k+1)+(n+j) = ((k+1)+n)+j`. For order `i=j+1`, put
`n=r+1-i` and prove `r=n+j`. The input cast along this equality moves
through the mixed product by `leftMixedProduct_rankCast`.
`derivativeOfOrderTargetTransport` identifies the order wrapper and
output cast with the target-rank derivative, using equality elimination
for the target rank and the number of steps separately. The same
identity on the second input restores its exact order-indexed derivative.
The target cast in the displayed proposition is consequently retained,
including at `n=0`.

For GL rank zero, the helper uses the independently published
`LeftMixedProductZeroRank.leftMixedProductZeroRankIso` for every order.
That proof evaluates compact induction from the whole group at `1`,
uses the trivial left inducing character and trivial GL₀ group action,
and sends `a ⊗ b` to `b ⊗ ULift.up a`. The arbitrary carrier of `A`
is retained. The published `ZeroRankTensor` maps
`[b ⊗ a] ↔ [b] ⊗ a` commute the entire character relation quotient
with the inert factor. Pullback, twist and rank-cast comparisons commute
each minus functor, iteration gives every order, and the inverse
binary-left-zero tensor comparison supplies the exact binary endpoint.
These are explicit inverse linear and equivariant maps, natural in both
input maps. This GL₀ argument uses no positive-rank 4.13(b) clause.

For vanishing, the helper inducts on `r` with arbitrary source transport
`k+1+r=n+j` and `r+1≤j`. When `r=0`, the first Phi step has a
subsingleton carrier by the published
`MirabolicProductMinus.leftPhiBoundary`; the remaining rank cast and
derivative preserve that property. At `r+1`, the published Phi
comparison moves the first step to `B`, and its component, mapped
through the remaining cast and derivative, transfers the induction
hypothesis backwards along an isomorphism. The helpers
`phiMinus_obj_rankCast` and `mirabolicRankCast_obj_trans` are equality
elimination, so all source transports remain actual transports.
Finally the order wrapper uses `j=i-1`; `r+1<i` implies `r+1≤j`.
If `k=0`, the valid-order upper bound contradicts `r+1<i`.

All positive-rank comparison components and inverses are compositions of
selected compatibility isomorphisms, their whiskerings, equality
isomorphisms, associators and unitors. Naturality follows on the entire
product category, so it includes both input maps simultaneously.
`Classical.choice` selects some isomorphism from each proved `Nonempty`;
the proposition does not identify that choice with the explicit witness
inside its proof. The witness formulas described for published
compatibilities below concern their provenance, without claiming such an
identification. The vanishing proof only eliminates `Nonempty` into Prop.

## Original source and published inputs

The registered original is I. N. Bernstein and A. V. Zelevinsky,
*Induced representations of reductive p-adic groups I*, Ann. Sci. ENS
(4) 10 (1977), 441–472, literature ID
`bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
Sections 3.2–3.5, printed pp.450–452 (one-based PDF pp.11–13),
give the minus functors and order convention; §4.12(II), printed
p.457 (PDF p.18), gives the mixed products. Proposition 4.13(b) and
Corollary 4.14(a), printed p.458 (PDF p.19), give the source scope,
and §7.2, printed p.471 (PDF p.32), gives the two-orbit argument for
4.13(b). These original passages and relevant page images were read
for this proof; a bounded supplied-source and errata-note search found
no applicable BZ77 entry.

The source derives 4.14(a) from 4.13(b). Here its positive-rank Psi,
Phi and P₁-boundary clauses enter only through their separately
published proofs. The order bookkeeping and categorical assembly are
internal derived content. The arbitrary-carrier GL₀ comparison is also
internal: the source does not state it separately and uses its zero
boundary convention at P₀.
The quotient/tensor construction agrees with BZ77 Proposition 1.9(g),
printed p.445 (PDF p.6), and is proved directly in Lean.

| Published Lean input | Verified role and publication |
| --- | --- |
| `MirabolicProductMinus.leftPsiCompatibility` | Exact left Psi clause; published at `5c739daf70eeb88f11ce9139aeb3ed04904874ca`. |
| `MirabolicProductMinus.leftPhiCompatibility` | Exact left Phi clause; published at `a76eaf5aaac38487c19b4cf2e7c9bd64e2493518`. |
| `MirabolicProductMinus.leftPhiBoundary` | Exact P₁ boundary; published. |
| `LeftMixedProductZeroRank.leftMixedProductZeroRankIso` | All-order arbitrary-carrier GL₀ natural comparison; published at `2003a7a6a41b5e54c3f790e0887743ed616ed614`. |
| `ZeroRankTensor` | Full quotient/tensor, pullback, twist, derivative and cast commutations; published at `9a8ca758097242bde4147f33304f43fceef22fa4`. |
| `OrderRecursion` | Definitional derivative recursion and cast laws; published. |
| `MixedProductRankCast` | Both-input natural rank transport; published. |

The Psi proof's `MirabolicProductMinusLeftPsiInduction` and
`Induction.BinaryPositiveCompact` inputs were published at
`2003a7a6a41b5e54c3f790e0887743ed616ed614` and
`9a8ca758097242bde4147f33304f43fceef22fa4`. The Phi proof's full
normalization, localized Mackey and rank-transport comparisons are
published inputs of its proof. Publication of
these prerequisites was checked separately from compilation.
All mathematics is imported by Lean name. No source citation, Prop
definition or consumer conclusion fills
a missing proof.

## Complete import and proof-dependency audit

The combined closure has 260 project modules including this entry: the
three new pairs of this proof and 257 published modules. All 514
published Lean/Markdown files are nonempty and byte-identical to Library
commit `8d926c3850083c700afa54adc0d07240e27fe799`. The target pair and its
entire dependency closure are unchanged. The only new or edited public
pairs are this entry, `LeftMixedProductHigher` and
`LeftMixedProductVanishing`. The complete list of 259 project imports,
excluding this entry, and the 125 external boundary imports appears below.
The external boundary is the set of directly encountered non-project
imports; it does not purport to expand Mathlib's internal import graph.

The audit checks mathematical proof provenance as well as imports. The
following distinctions matter because importing a proposition or a generic
construction does not prove a consumer assertion.

| Actual input or potentially broad import | Body/provenance finding |
| --- | --- |
| New higher-order and vanishing helpers | Natural-isomorphism composition, equality transport, arithmetic and induction use only the published Psi, Phi, boundary and arbitrary-carrier GL₀ comparisons. The explicit Phi argument in each helper is discharged by the published exact theorem in the entry. |
| Published left Psi comparison | The actual radical projection, surjectivity, kernel, subgroup topology and smoothness conditions are proved. Normal-coinvariant comparison, split quotient and character twist identify the full localized compact induction. Relation-kernel arguments, local sections, cutoff and compact averaging prove its lower maps; no consumer finiteness input is used. |
| Psi determinant normalization | Determinant factorization and a real-power identity identify the whole coefficient scalar with the binary parabolic half modulus, retaining both blocks. No scalar comparison remains as a premise. |
| Positive binary compact comparison | Pointwise coefficient transport, binary tensor action/map laws and compact-inclusion bijectivity identify the actual binary product. Parabolic quotient compactness follows from `G=P K`, compactness of the integral subgroup and the elementary column-reduction proof of Iwasawa decomposition. |
| Published left Phi localization | Two-orbit coverage and the actual closed-subgroup Mackey restriction sequence give the cycle and identity pieces. Right exactness of the entire character relation-span quotient and vanishing of the entire localized cycle make the localized identity projection bijective. This is the proved general quotient/Mackey route, without using minus exactness. |
| Phi stages and scalar normalization | The positive-character stages comparison retains the full compact-function and quotient carriers. `leftPhiAmbientInductionEquiv` moves the ambient inverse-half determinant character through compact induction, multiplying values by the character and inversely by its reciprocal. The source action proves the complete identity `χ(h)=λ_(K,r)(a,q) α_r(q)`: ambient inverse-half times higher covariance equals lower covariance times source Phi normalization, with actual determinant norms and no residual twist. |
| Phi identity/source coefficient and host transport | The map `id ⊗ q_B` is onto with kernel exactly the identity-orbit radical relation span. The full normalized identity/source equivalence and both-input naturality, compact-induction transport/transitivity and actual inverse rank maps give the lower source comparison. The final Phi proof composes these natural equivalences and uses fullness/faithfulness of `SmoothRep.toRep` to return to the exact smooth host functors. |
| Published P₁ boundary | The actual quotient relations and nontrivial character kill the full boundary carrier; the subsequent rank casts and minus functors preserve subsingleton carriers. No finite-length or detection theorem is invoked. |
| Arbitrary-carrier GL₀ comparison and `ZeroRankTensor` | Whole-group evaluation, trivial GL₀ action/character, swap/lift and binary-left-zero tensor equivalence construct the endpoints. The direct quotient maps `[v ⊗ a] ↔ [v] ⊗ a` are inverse on all generators and commute with actions, both maps, pullbacks, twists and rank casts. Iteration supplies every order without a positive-rank compatibility assumption. |
| `Mirabolic.MixedProducts` and `Induction.BinaryProduct` | These supply actual subgroup matrices, coefficients, normalized compact/smooth induction, tensor models and full functor maps unchanged. Their lower mathematical inputs are matrix identities, smoothness, tensor algebra and induction constructions. |
| `MirabolicProductRestrictionFactors` and `SplitStagesComparison` | The binary route uses `FiniteTensor.binaryLinearEquiv` with its external action/map laws, and pointwise `Induction.compactInducedEquiv`. The Phi route additionally uses the independently proved actual Mackey and stages comparisons described above. No GL Leibniz or segment geometric-lemma consumer supplies an input. |
| `Derivative.Homogeneity` | This imported module defines the order wrapper, actual rank casts and homogeneity predicates and proves elementary zero-carrier facts. It supplies no Ze80 5.3 or 6.2 theorem. Its name does not constitute use of the homogeneity consumers listed below. |
| `Classification.Supercuspidal`, `SupercuspidalContragredientAux` and `SupercuspidalContragredientStatement` | These occur in the transitive closure through `Smooth.SmallRealizationProof`. Their bodies provide the actual admissibility/Jacquet-vanishing predicate, class packaging, equivalence invariance, conjugate-coinvariant equivalence, conditional admissibility/irreducibility transfer and an unproved duality proposition. They contain no segment classification, exhaustion, two-supercuspidal product or coinvariant-finiteness theorem. No conclusion listed below follows merely from these definitions or conditional interfaces; none supplies a derivative-comparison premise. |
| Lower Whittaker/Rankin–Selberg constructions | Character and matrix-coefficient constructions, compatible Haar quotient measures, quotient integration, compact-orbit averaging, cutoff, local sections and unimodularity are used in the lower induction/stages route. They do not assume supercuspidal, irreducible, Levi-cuspidal or all-character coinvariant finiteness. |
| `Category.Basic` and `Filtration.Definitions` | These define categorical finite length and filtrations. No mirabolic finite-length theorem or Leibniz filtration proof is used. |
| Compatibility and derivative statement modules | These supply exact proposition types and functor definitions unchanged. The left Psi, Phi and boundary clauses enter only through published proofs. Other proposition definitions supply no proved comparison. |

## Results not used, first set: the Ze80 6.2 route

Each row rules out both the named conclusions and the modules proving them and
their transitive consequences. The reasons refer to the actual construction
audit above, not just to absence of an identifier.

| Result not used | Audit result |
| --- | --- |
| Ordered-socle existence / `OrderedMultisegmentSocleExistence`; socle exhaustion / `MultisegmentSocleExhaustion` | No socle, essential-subobject or ordered-existence input; components come from quotient and induction equivalences. |
| Analytic segment classification | No segment or analytic classification input. |
| Unlinked segment-socle product irreducibility | No segment-product irreducibility argument or criterion supplies an input. |
| Final `SegmentSocleProductIrreducibility` | No criterion or consequence supplies an input. |
| `AdjacentUnlinkedSegmentSocleSwap`, adjacent commutation, and `TwoSegmentSocleCommutation` | No socle-product swap or commutation theorem; the tensor swap in GL₀ is elementary linear algebra. |
| Special-head product criterion / `SegmentHeadProductIrreducibility` | No head or special-head criterion is used. |
| Special-head multisegment exhaustion | No exhaustion input. |
| Ordered special/strong-head existence | No head-existence input. |
| Quotient coverage | No representation-coverage theorem; quotient universal properties here are elementary module operations. |
| Tempered block uniqueness | No tempered decomposition or uniqueness input. |
| `SquareIntegrableLanglandsClassification` | No square-integrable or Langlands classification input. |
| Square-integrable exhaustion; regular exhaustion | Neither exhaustion result nor a consequence is used. |
| `GenericSegmentProductUniqueness` | No genericity or segment uniqueness input. |
| Ordered special-segment conversion | No head/socle conversion input. |
| Forward special essential square-integrability / `SegmentSpecialEssentialSquareIntegrability` | No square-integrability input. |
| Individual special-head/reverse-socle existence | No individual segment-existence input. |
| Individual segment-socle/reverse-head existence | No individual segment-existence input. |
| `SegmentFullJacquetFormula`, its statement/arrangement and the module proving it | No segment Jacquet formula; the localized coefficient computation is general and proved directly. |
| `SegmentHeadJacquetFormula` | No segment head Jacquet input. |
| `SegmentSocleJacquetFormula` | No segment socle Jacquet input. |
| `SegmentSpecialJacquetExponentNormFormula` | No segment exponent formula; determinant factors are computed from matrices and characters. |
| Combined Ze80 §5.4 reduction and strong-indecomposability conclusion, including its consumer | No detection, indecomposability or combined reduction input. |
| `TwoSupercuspidalNonadjacentProductIrreducible`; `TwoSupercuspidalProductStructure`, including adjacent composition/Jacquet conjuncts | No such supercuspidal-product or two-factor structure theorem; the elementary predicate and conjugation imports are accounted for above. |
| Ze80 §3.5 and §9.6 segment derivatives; segment-socle derivative results | No segment derivative formula or segment-socle derivative result is used. Order recursion is definitional; Psi, Phi, boundary and GL₀ comparisons enter through their published proofs. |
| Ze80 4.2 or 9.7 product criteria, Ze80 9.3 analytic/square-integrability results, and any classification/exhaustion theorem | None is used. No linked-pair converse is used circularly to establish Proposition 1.11. |
| Consumer homogeneity: Ze80 6.2, Ze80 5.3 and its proof | No consumer homogeneity theorem or proof dependency. `RestrictedProductLevel`, `SegmentSocleProductHomogeneityInduction` and `SegmentSocleProductCaseTwo` are absent from the closure. |
| All-rank GL Leibniz consumer | No Leibniz theorem, filtration proof or downstream consequence is used. |
| Minus exactness | No input from minus exactness and no duplicate of it. |

## Results not used, second set: the all-rank Leibniz route

All conditions in the preceding table also hold for the second set:
in particular its repeated classification, exhaustion, two-supercuspidal,
individual existence, segment Jacquet and analytic restrictions are checked by
those same rows without weakening. The following rows cover the additional
named conclusions, and the modules proving them, of the all-rank Leibniz route
and its exact-derivative statement.

| Additional or more explicitly named condition | Audit result |
| --- | --- |
| `UnlinkedSegmentSocleProductIrreducible`, `LinkedSegmentSocleReverseProductStructure`, `LinkedSegmentSoclePairReducible` | None is an input. The induction/coinvariant equivalences are constructed independently of these segment-product irreducibility conclusions. |
| `JuxtaposedSegmentSocleReverseProductStructure`, `LinkedSegmentSocleReverseProductQuotientHom`, and the modules proving them | No segment quotient-homomorphism or juxtaposed-product input. |
| Proof of adjacent socle commutation (`AdjacentUnlinkedSegmentSocleSwap`) | Absent, as is the statement it proves. |
| `TwoSegmentSocleCommutation` | No commutation result or proof of one. The GL₀ tensor swap uses tensor algebra only. |
| `LinkedSegmentSocleGluing` | No gluing or extension classification input. |
| Every segment derivative, existence, Jacquet or classification conclusion, and proofs depending on them | None is used. No cuspidal or segment derivative theorem supplies the tensor or localization maps. |
| `Langlands.Whittaker.SupercuspidalCoinvariantFinitenessStatement`, the all-character single-block result, their proofs and consequences | No supercuspidal/all-character finiteness input; compact averaging in induction is a direct local construction. |
| `Langlands.Whittaker.IrreducibleCoinvariantFinitenessStatement` | No irreducible Whittaker-finiteness input or downstream consequence. |
| `LeviCuspidalCoinvariantFinitenessStatement` and its proof | No Levi/cuspidal finiteness input or downstream consequence. |
| Mirabolic finite-length route using these finiteness results | No mirabolic finite-length proof is used. The categorical finite-length definition in `Category.Basic` proves none of these assertions. |
| General derivative/tensor results must not be supplied by their consumers | Psi, Phi, boundary and GL₀ comparisons are independently published constructions; tensor commutation is proved by quotient maps. No consumer assumption fills a missing proof. |
| Shared character, Jacquet, top-localization, exactness, geometric lemma, cuspidal-support and finite-length infrastructure requires an independence check | The actual character/localization/induction bodies are covered above, including proved quotient right exactness and the actual closed-subgroup Mackey sequence. No top-localization consumer, minus-exactness conclusion, GL Leibniz/geometric-lemma consumer, cuspidal-support theorem or mirabolic finite-length theorem supplies an input. |
| BZ77 4.13(b,c), 4.13(d), 4.14(b) and Whittaker finiteness | Their proofs are not duplicated here. |

A nested-comment-aware scan of all 260 project Lean modules checked
31 exact names,
including the declarations named above and the three homogeneity
consumer modules. The exact-name hits were
only the derivative/compatibility statement imports and imports
of `Derivative.Homogeneity`. A broader segment, socle, head, classification,
supercuspidal, finite-length, coinvariant-finiteness, Leibniz and homogeneity
scan found only the elementary predicate, class, conditional duality and
zero-carrier material identified above, including the supercuspidal imports.
No consumer declaration named above, proof hole, invented axiom or forbidden
execution construct was found. This scan supports the mathematical body
and provenance audit; it is not a substitute for a semantic reading of the proofs.

The full readable declaration inspection and the Lake build
confirm the stated telescope, independent `uF,uV`, no extra premise and
only `propext`, `Classical.choice` and `Quot.sound`.

## Complete project import closure

All direct and transitive project imports, excluding this entry, follow.
The Lean and Mathlib commits are respectively
`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b` and
`5ed2965256430c3649e86755f9576b54eca72435`.

```text
Langlands.Analysis.Local.ModularCompactAverage
Langlands.Analysis.Local.QuotientAutomorphismProof
Langlands.Analysis.Local.QuotientAutomorphismStatement
Langlands.Analysis.Local.QuotientAverageReal
Langlands.Analysis.Local.QuotientAveragingKernel
Langlands.Analysis.Local.QuotientComplex
Langlands.Analysis.Local.QuotientFunctional
Langlands.Analysis.Local.QuotientMass
Langlands.Analysis.Local.QuotientMeasure
Langlands.Analysis.Local.QuotientMeasureExistence
Langlands.Analysis.Local.QuotientMeasureExistenceStatement
Langlands.Analysis.Local.QuotientMeasurePrerequisites
Langlands.Analysis.Local.QuotientPositiveLifting
Langlands.Analysis.Local.QuotientTopology
Langlands.Analysis.Local.QuotientTranslation
Langlands.Analysis.Local.SplitKernelQuotient
Langlands.Group.GL.Basic
Langlands.Group.GL.BlockModulus
Langlands.Group.GL.Blocks
Langlands.Group.GL.CompactOpen
Langlands.Group.GL.CountabilityProof
Langlands.Group.GL.CountabilityStatement
Langlands.Group.GL.Maps
Langlands.Group.GL.Mirabolic
Langlands.Group.GL.MirabolicMixedOrbitCoverageProof
Langlands.Group.GL.MirabolicMixedOrbitCoverageStatement
Langlands.Group.GL.MirabolicMixedOrbitData
Langlands.Group.GL.MirabolicMixedOrbitRadicals
Langlands.Group.GL.MirabolicMixedOrbitSectionCoefficients
Langlands.Group.GL.MirabolicMixedOrbitSections
Langlands.Group.GL.MirabolicMixedOrbitSpecializations
Langlands.Group.GL.MirabolicMixedOrbitStages
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
Langlands.HarmonicAnalysis.HaarConjugacy
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
Langlands.Representation.Classification.Supercuspidal
Langlands.Representation.Classification.SupercuspidalContragredientAux
Langlands.Representation.Classification.SupercuspidalContragredientStatement
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
Langlands.Representation.Derivative.LeftMixedProductHigher
Langlands.Representation.Derivative.LeftMixedProductVanishing
Langlands.Representation.Derivative.LeftMixedProductZeroRank
Langlands.Representation.Derivative.MinusVanishing
Langlands.Representation.Derivative.MirabolicCharacter
Langlands.Representation.Derivative.MirabolicDeterminant
Langlands.Representation.Derivative.MirabolicLatticeBox
Langlands.Representation.Derivative.MirabolicMinus
Langlands.Representation.Derivative.MirabolicMixedOrbitCharacters
Langlands.Representation.Derivative.MirabolicProductMinusBoundary
Langlands.Representation.Derivative.MirabolicProductMinusCompatibilityStatement
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhi
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiCoefficient
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiCompactComparison
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiHaar
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiHostTransport
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiIdentityComparison
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiInductionNormalization
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiLocalization
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiMackeyLocalization
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiNormalization
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiNormalizedSection
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiSection
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiSourceAction
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiSourceComparison
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiStagesComparison
Langlands.Representation.Derivative.MirabolicProductMinusLeftPsi
Langlands.Representation.Derivative.MirabolicProductMinusLeftPsiInduction
Langlands.Representation.Derivative.MirabolicProductMinusPhiKernelComparison
Langlands.Representation.Derivative.MirabolicProductRestrictionFactors
Langlands.Representation.Derivative.MirabolicProductRestrictionMackey
Langlands.Representation.Derivative.MirabolicProductRestrictionOrbits
Langlands.Representation.Derivative.MirabolicProductRestrictionTransport
Langlands.Representation.Derivative.MixedProductDerivativeStatement
Langlands.Representation.Derivative.MixedProductRankCast
Langlands.Representation.Derivative.OrderRecursion
Langlands.Representation.Derivative.ZeroRankTensor
Langlands.Representation.Dual.Definitions
Langlands.Representation.Filtration.Definitions
Langlands.Representation.Filtration.QuotientFirstIso
Langlands.Representation.Geometric.ClosedSubgroupAssembly
Langlands.Representation.Geometric.ClosedSubgroupDefinitions
Langlands.Representation.Geometric.ClosedSubgroupMackeyProof
Langlands.Representation.Geometric.ClosedSubgroupStatement
Langlands.Representation.Geometric.CompactOrbitRestriction
Langlands.Representation.Geometric.CosetAction
Langlands.Representation.Geometric.CosetOrbitHomeomorph
Langlands.Representation.Geometric.OrbitRestriction
Langlands.Representation.Geometric.OrbitSectionExtensionProof
Langlands.Representation.Geometric.OrbitSectionExtensionStatement
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
Langlands.Representation.Induction.SplitKernelCharacterExtension
Langlands.Representation.Induction.SplitKernelCompact
Langlands.Representation.Induction.SplitKernelCovariance
Langlands.Representation.Induction.SplitKernelEquivariant
Langlands.Representation.Induction.SplitKernelHaarTrivial
Langlands.Representation.Induction.SplitKernelIntegral
Langlands.Representation.Induction.SplitKernelLocalizationData
Langlands.Representation.Induction.SplitKernelSectionAction
Langlands.Representation.Induction.SplitQuotientProof
Langlands.Representation.Induction.SplitQuotientStatement
Langlands.Representation.Induction.SplitStagesCharacterComparison
Langlands.Representation.Induction.SplitStagesCharacterComparisonStatement
Langlands.Representation.Induction.SplitStagesCharacterIntegrand
Langlands.Representation.Induction.SplitStagesComparison
Langlands.Representation.Induction.SplitStagesRetraction
Langlands.Representation.Induction.StructuralStatement
Langlands.Representation.Induction.SurjectivityProof
Langlands.Representation.Induction.SurjectivityStatement
Langlands.Representation.Jacquet.CharacterAveraging
Langlands.Representation.Jacquet.Coinvariants
Langlands.Representation.Jacquet.ExactProof
Langlands.Representation.Jacquet.ExactStatement
Langlands.Representation.Jacquet.Localization
Langlands.Representation.Jacquet.LocalizationExactnessProof
Langlands.Representation.Jacquet.LocalizationExactnessStatement
Langlands.Representation.Jacquet.LocalizationTransport
Langlands.Representation.Jacquet.PositiveCharacter
Langlands.Representation.Jacquet.SmoothTwist
Langlands.Representation.MatrixCoefficient.Definitions
Langlands.Representation.MatrixCoefficient.LawsProof
Langlands.Representation.MatrixCoefficient.LawsStatement
Langlands.Representation.Mirabolic.MixedProducts
Langlands.Representation.OrbitSpan
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
Langlands.Representation.Smooth.Admissibility.EquivalenceProof
Langlands.Representation.Smooth.Admissibility.EquivalenceStatement
Langlands.Representation.Smooth.Contragredient.CompactDualityProof
Langlands.Representation.Smooth.Contragredient.CompactDualityStatement
Langlands.Representation.Smooth.Contragredient.Definitions
Langlands.Representation.Smooth.Contragredient.FixedVectorsDefinitions
Langlands.Representation.Smooth.Contragredient.LawsProof
Langlands.Representation.Smooth.Contragredient.LawsStatement
Langlands.Representation.Smooth.Definitions
Langlands.Representation.Smooth.FixedVectors.Definitions
Langlands.Representation.Smooth.SmallRealizationProof
Langlands.Representation.Smooth.SmallRealizationStatement
Langlands.Representation.Smooth.SmoothPart.BasicProof
Langlands.Representation.Smooth.SmoothPart.BasicStatement
Langlands.Representation.Smooth.SmoothPart.Definitions
Langlands.Representation.Smooth.SmoothPart.FixedVectorsDefinitions
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
Langlands.Representation.Unitary.Basic
Langlands.Representation.Whittaker.Algebraic
Langlands.Representation.Whittaker.GeneralLinear
Langlands.Representation.Whittaker.Iwasawa
Langlands.Topology.CompactNormCharacter
Langlands.Topology.CompactOpen.ConjugationStabilizer
Langlands.Topology.CompactOpen.NeighborhoodBasis
Langlands.Topology.CompactOpen.NeighborhoodBasisStatement
Langlands.Topology.Nonarchimedean.Subgroup
```

## Complete external import boundary

```text
Lean.Elab.Tactic.Omega
Mathlib.Algebra.BigOperators.Fin
Mathlib.Algebra.BigOperators.Finprod
Mathlib.Algebra.BigOperators.Group.Finset.Basic
Mathlib.Algebra.BigOperators.Pi
Mathlib.Algebra.CharP.Basic
Mathlib.Algebra.Group.Equiv.TypeTags
Mathlib.Algebra.Group.Hom.Instances
Mathlib.Algebra.Group.Subgroup.Ker
Mathlib.Algebra.Module.ULift
Mathlib.Algebra.Order.Archimedean.Basic
Mathlib.Algebra.Order.BigOperators.Group.Finset
Mathlib.Algebra.Polynomial.Lifts
Mathlib.Algebra.Ring.GeomSum
Mathlib.Analysis.Complex.Basic
Mathlib.Analysis.Complex.Circle
Mathlib.Analysis.Fourier.FourierTransform
Mathlib.Analysis.InnerProductSpace.Defs
Mathlib.Analysis.Matrix.MeasurableSpace
Mathlib.Analysis.Normed.Module.FiniteDimension
Mathlib.Analysis.Normed.Unbundled.SpectralNorm
Mathlib.Analysis.Real.Sqrt
Mathlib.Analysis.SpecialFunctions.Complex.Circle
Mathlib.Analysis.SpecialFunctions.Pow.Complex
Mathlib.Analysis.SpecialFunctions.Pow.NNReal
Mathlib.Analysis.SpecialFunctions.Pow.Real
Mathlib.Basic.Complex.Basic
Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
Mathlib.CategoryTheory.Pi.Basic
Mathlib.CategoryTheory.Products.Basic
Mathlib.CategoryTheory.Skeletal
Mathlib.Data.Fin.Rev
Mathlib.Data.Int.LeastGreatest
Mathlib.Data.Matrix.Block
Mathlib.Data.Nat.Find
Mathlib.FieldTheory.Finite.Basic
Mathlib.GroupTheory.Coset.Defs
Mathlib.GroupTheory.DoubleCoset
Mathlib.GroupTheory.GroupAction.ConjAct
Mathlib.GroupTheory.GroupAction.Quotient
Mathlib.GroupTheory.Subgroup.Centralizer
Mathlib.LinearAlgebra.Dual.Lemmas
Mathlib.LinearAlgebra.Isomorphisms
Mathlib.LinearAlgebra.Matrix.Block
Mathlib.LinearAlgebra.Matrix.Diagonal
Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
Mathlib.LinearAlgebra.Matrix.Kronecker
Mathlib.LinearAlgebra.Matrix.Permutation
Mathlib.LinearAlgebra.Matrix.Reindex
Mathlib.LinearAlgebra.Matrix.Transvection
Mathlib.LinearAlgebra.PiTensorProduct.Basic
Mathlib.Logic.Equiv.Fin.Basic
Mathlib.MeasureTheory.Constructions.Pi
Mathlib.MeasureTheory.Function.LocallyIntegrable
Mathlib.MeasureTheory.Function.SimpleFunc
Mathlib.MeasureTheory.Group.Integral
Mathlib.MeasureTheory.Group.LIntegral
Mathlib.MeasureTheory.Group.ModularCharacter
Mathlib.MeasureTheory.Integral.Bochner.Basic
Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
Mathlib.MeasureTheory.Integral.Bochner.Set
Mathlib.MeasureTheory.Integral.Marginal
Mathlib.MeasureTheory.Integral.Prod
Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
Mathlib.MeasureTheory.Measure.Haar.Basic
Mathlib.MeasureTheory.Measure.Haar.DistribChar
Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
Mathlib.MeasureTheory.Measure.Haar.Unique
Mathlib.MeasureTheory.Measure.Regular
Mathlib.MeasureTheory.Measure.Typeclasses.Finite
Mathlib.NumberTheory.LocalField.Basic
Mathlib.NumberTheory.Padics.LocalField
Mathlib.NumberTheory.Padics.RingHoms
Mathlib.Order.Atoms
Mathlib.RepresentationTheory.Basic
Mathlib.RepresentationTheory.Coinduced
Mathlib.RepresentationTheory.Coinvariants
Mathlib.RepresentationTheory.Intertwining
Mathlib.RepresentationTheory.Invariants
Mathlib.RepresentationTheory.Irreducible
Mathlib.RepresentationTheory.Rep.Basic
Mathlib.RepresentationTheory.Rep.Res
Mathlib.RepresentationTheory.Subrepresentation
Mathlib.RingTheory.DedekindDomain.IntegralClosure
Mathlib.RingTheory.FiniteLength
Mathlib.RingTheory.Finiteness.Basic
Mathlib.RingTheory.Ideal.Quotient.Operations
Mathlib.RingTheory.Noetherian.Basic
Mathlib.RingTheory.Noetherian.Defs
Mathlib.RingTheory.RamificationInertia.Basic
Mathlib.RingTheory.SimpleModule.Basic
Mathlib.RingTheory.Valuation.Integral
Mathlib.Tactic.Linarith
Mathlib.Tactic.NoncommRing
Mathlib.Topology.Algebra.ContinuousMonoidHom
Mathlib.Topology.Algebra.Group.Basic
Mathlib.Topology.Algebra.Group.Matrix
Mathlib.Topology.Algebra.Group.OpenMapping
Mathlib.Topology.Algebra.Group.Pointwise
Mathlib.Topology.Algebra.Group.Quotient
Mathlib.Topology.Algebra.Group.Subgroup
Mathlib.Topology.Algebra.Group.Units
Mathlib.Topology.Algebra.Module.FiniteDimension
Mathlib.Topology.Algebra.MulAction
Mathlib.Topology.Algebra.Nonarchimedean.Basic
Mathlib.Topology.Algebra.OpenSubgroup
Mathlib.Topology.Algebra.ProperAction.Basic
Mathlib.Topology.Algebra.Ring.Compact
Mathlib.Topology.Algebra.Support
Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology
Mathlib.Topology.Algebra.Valued.NormedValued
Mathlib.Topology.Baire.LocallyCompactRegular
Mathlib.Topology.Bases
Mathlib.Topology.Compactness.Compact
Mathlib.Topology.Compactness.LocallyCompact
Mathlib.Topology.Compactness.SigmaCompact
Mathlib.Topology.Connected.TotallyDisconnected
Mathlib.Topology.ContinuousMap.CompactlySupported
Mathlib.Topology.Homeomorph.Lemmas
Mathlib.Topology.Homeomorph.Quotient
Mathlib.Topology.Instances.NNReal.Lemmas
Mathlib.Topology.LocallyClosed
Mathlib.Topology.LocallyConstant.Basic
Mathlib.Topology.Order.Compact
Mathlib.Topology.UrysohnsLemma
```
