# The natural normalized right Psi compatibility

Author: Worker 837.

This module proves the unchanged published proposition
`Langlands.Derivative.MirabolicProductMinus.RightPsiCompatibility.{uF,uV} F T`
from `MirabolicProductMinusCompatibilityStatement`. Its entry theorem is

```lean
theorem Langlands.Derivative.MirabolicProductMinus.rightPsiCompatibility
    (T : F.TopologicalData) : RightPsiCompatibility.{uF, uV} F T
```

for every `{p : ℕ}`, `[Fact p.Prime]`, `F : PadicField.{uF} p` and
`T : F.TopologicalData`, with independent universes `uF` and `uV` and no
further hypotheses. For every positive GL rank and every source mirabolic
rank, including the source `P_1`, it constructs a natural isomorphism

```text
Ψ⁻(τ × ρ) ≅ Ψ⁻τ × ρ.
```

Both products and both minus functors are the actual published normalized
functors with their actual maps. The target keeps the actual rank transport
`generalLinearRankCast T (Nat.add_comm r (k+1))`. This focused proof
establishes the right Psi clause of BZ77 Proposition 4.13(c), component 4 of
the host task. The Phi comparisons, the Phi sequence and the other clauses of
the six-part host proposition are separate obligations.

## Original and derived provenance

The original is I. N. Bernstein and A. V. Zelevinsky, *Induced
representations of reductive p-adic groups I*, Ann. Sci. ENS (4) 10 (1977),
441–472; registered source `bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`. The
relevant passages are:

- §1.8, printed pp.444–445 (PDF pp.5–6): normalized induction;
- §§3.1–3.2, printed pp.450–451 (PDF pp.11–12): the mirabolic radical and
  the minus functors;
- §4.12, printed pp.456–458 (PDF pp.17–19), case (III): the right mixed
  product, with its inducing subgroup and character.

Proposition 4.13(c), printed p.458 (PDF p.19), states `Ψ⁻(τ × ρ) ≅ Ψ⁻(τ) × ρ`
for `τ ∈ Alg P_m` and `ρ ∈ Alg G_k`. The sentence after (d) makes all its
morphisms functorial and sets `P_0 = 0`. §7.2, printed p.471 (PDF p.32),
proves this with the geometric lemma, Theorem 5.2: for `Ψ⁻`,
`N = G_(n-1)`, `V = V_n`, and there is only one orbit. The details are left
to the reader.

The proof route and all intermediate declarations of this module and its
three helper modules are derived internal content. The proof does not apply
the geometric lemma or assume BZ77's compatibility. It computes the radical
coinvariants of the compact induction directly with the published two-stage
comparison `Induction.splitStagesCompactEquiv`, which is the one-orbit
computation made explicit. It then compares the result with the positive
binary product by the published `binaryPositiveCompactEquiv`.

## Parameters, ranks, carriers and functors

All topologies and topological group instances come from the supplied `T`.
The proposition quantifies `k, r : ℕ` and pairs of inputs
`τ : SmoothRep ℂ (mirabolic r F.Carrier)` and
`ρ : SmoothRep ℂ (GL_(k+1)(F))`. Here `mirabolic r = P_(r+1)` and
`psiMinus T r : P_(r+1) → GL_r`. In BZ77's notation `m = r + 1` and
`k = k + 1`.

- The source side is `rightMixedProductFunctor (k+1) r ⋙ psiMinus ((k+1)+r)`.
  The right mixed product (case (III)) has source group `P_((k+1)+r+1)`.
- The target side is
  `(psiMinus T r).prod 𝟭 ⋙ binaryNormalizedProductFunctor r (k+1) ⋙ generalLinearRankCast T (Nat.add_comm r (k+1))`.
  It is a representation of `GL_((k+1)+r)`.
- Both sides have carrier universe `max uF uV`.

The shift `phiMinus T ψ r : P_(r+2) → P_(r+1)` does not occur in this clause.

At `r = 0` the source is `P_1`, and `Ψ⁻τ` is a representation of `GL_0`
whose carrier is the entire carrier of `τ`. The binary product with a zero
first rank is the published rank-zero model `binaryLeftZeroTensorFunctor`.
No `P_0` is introduced, and no positive-rank GL factor is replaced by `GL_0`
or a unit object. Zero objects, arbitrary smooth objects and repeated factors
are all allowed. No admissibility, irreducibility, genericity, finite
dimension, finite length, chosen vector, chosen unit or universe saturation
is assumed.

## Helper modules

The candidate adds three helper pairs in
`Langlands/Representation/Derivative/`:

- `MirabolicProductMinusRightPsiZero` proves the case `r = 0`
  (`rightPsiCompatibility_zero`). It also defines the explicit rank cast
  `generalLinearCastHom` and `generalLinearRankCastIso`, which identify the
  published `generalLinearRankCast` with pullback along that cast.
- `MirabolicProductMinusRightPsiGroups` defines:
  - the parabolic `Q ⊆ GL_(m+r)` and its preimage `P ⊆ P_(m+r+1)`;
  - the diagonal blocks `A ∈ GL_r` and `D ∈ GL_m` of `l = [[A, X], [0, D]] ∈ Q`;
  - the kernel `N = H ∩ ker(projection)` and the isomorphism `N ≅ V_(r+1)`.

  It computes the Haar ratio character of the comparison as `|det D|`.
- `MirabolicProductMinusRightPsiCoefficient` identifies the coefficient of
  the comparison with `Ψ⁻τ ⊗ ρ` and proves its action
  `δ^(1/2)(l) (Ψ⁻τ)(A) ⊗ ρ(D)` and its naturality.

Their Markdown files describe each declaration.

## The positive-rank comparison

Write `m = k + 1`, `r = r' + 1` and `n = m + r`. Set:

- `G = P_(n+1) = mirabolic n` and `L = GL_n`;
- `projection : G → L`, with section `levi`;
- `H = rightSubgroup m r`, the case (III) subgroup;
- `σ = rightPsiInducingCoefficient T τ ρ = twist χ_R (τ ⊠ ρ)`, so that the
  mixed product is `compactInduced H σ`;
- `P = rightPsiStages`, `K = P.comap levi`,
  `B = BlockShape.binary r m hr hm`.

For each `X = (τ, ρ)` the component `E X` composes these equivalences of
representations of `GL_n`:

1. `psiMinusCoinvariantsEquiv`. The published `Ψ⁻` of a representation `A`
   is the localization of `A` at `(radical, 1)` twisted by `|det|^(-1/2)`.
   Its relations equal the coinvariant relations of `ker projection`
   (`relations_congr`, `ker_projection`, `Jacquet.Localization.relations_one`).
   So `Ψ⁻A` is `twist ψc ((A.toCoinvariants (ker projection)).comp levi)`
   with `ψc = psiMinusCharacter T n`.
2. `twistEquiv ψc` of the published `splitStagesCompactEquiv`. Its data are
   `projection`, `levi`, `P`, `H` and `σ`. It identifies the
   `ker projection`-coinvariants of `compactInduced H σ`, restricted along
   `levi`, with `compactInduced K κ`. The coefficient `κ` is the published
   descended coefficient action on the `I`-coinvariants of `σ`, twisted by the
   complex Haar ratio character `splitKernelHaarRatio`. All hypotheses are
   discharged here:
   - continuity of `projection` and `levi`;
   - closedness of `P`, `H` and `ker projection`, and the containments;
   - `levi l ∈ H` for `l ∈ K`;
   - smoothness of `σ` (published `isSmooth_rightInducingRepresentation` and
     `isSmooth_twist_iff`);
   - a compact open basis of `P_(n+1)` (`mirabolic_compactOpenBasis`, via the
     nonarchimedean subgroup topology and `compactOpenSubgroupBasis`);
   - a compact open basis of the kernel, transported from the published
     radical basis along `splitStagesKernelContinuousEquiv`;
   - Borel structures and local compactness;
   - left and right invariant Haar measures, using
     `Haar.compactOpenCoverUnimodularity`;
   - a compatible quotient measure from
     `QuotientIntegration.compatibleMeasureExists`.
3. The published `compactInductionTwistEquiv` moves the twist by `ψc`
   inside: `twist ψc (compactInduced K κ) ≅ compactInduced K (twist ψc|K κ)`.
4. `rightPsiCompactEquivOf` with `X' = (Ψ⁻τ, ρ)`. It uses the coefficient
   identification `rightPsiCoefficientEquiv` and its action law
   `rightPsiCoefficientEquiv_action`: `l ∈ K` acts on `Ψ⁻τ ⊗ ρ` by
   `δ^(1/2)(l) (Ψ⁻τ)(A) ⊗ ρ(D)`. In that law the three source scalars
   `|det l|^(-1/2)`, the Haar ratio `|det D|` and
   `χ_R(diag(l, 1)) = |det A|^(m/2) |det D|^(-(r+1)/2)` multiply exactly to
   `δ^(1/2)(l) · |det A|^(-1/2)` (`rightPsi_scalar_eq`). The factor
   `|det A|^(-1/2)` is the `Ψ⁻` normalization inside `(Ψ⁻τ)(A)`.
   `rightPsiCompactEquivOf` then performs three steps:
   - the published `compactInducedTransport` along
     `rightPsiCastContinuous : GL_(m+r) ≃ₜ* GL_(r+m)`, which carries `K` onto
     `B.parabolic` (`mem_rightPsi_iff`) and the coefficient onto the published
     `binaryPositiveCoefficient` (`rightPsi_transport_equivariant`);
   - the published `binaryPositiveCompactEquiv`, which identifies compact
     induction from `B.parabolic` with the positive binary product (its
     inclusion into smooth induction is bijective because the actual parabolic
     quotient is compact), restricted along the cast by `restrictAlongEquiv`;
   - `compEquivOfEq`, which replaces the cast by `generalLinearCastHom`
     (`rightPsiCastContinuous_toMonoidHom`).

The result is a representation equivalence onto the object of
`rightPsiPosTarget T k r'`. That functor is `(psiMinus T r).prod 𝟭`, then the
unchanged `binaryPositiveProductFunctor`, then pullback along the cast. No
scalar or character is discarded at any step.

## Naturality and the exact proposition

For a pair morphism `φ = (φ₁, φ₂)`, the actual mixed-product map acts on the
coefficient by
`t₀ = twistIntertwining χ_R (pullbackMap rightProjection (externalMap φ₁ φ₂))`.
`hEnat` composes four naturality laws by `chain_natural₄`:

1. `psiMinusCoinvariantsEquiv_natural`, proved by quotient induction;
2. the published `splitStagesCompactEquiv_natural` at `t₀`;
3. `compactInductionTwistEquiv_natural`, proved by evaluation;
4. `rightPsiCompactEquivOf_natural`, with
   `rightPsiCoefficientEquiv_natural`. The latter shows that `t₀` induces
   `Ψ⁻(φ₁) ⊗ φ₂` on the coefficient. `rightPsiCompactEquivOf_natural` reduces
   by evaluation to the published `binaryPositiveCoefficientMap_tensor`.

So `E` commutes with `Ψ⁻` of the actual mixed-product map and with the actual
binary-product map, in both inputs. `NatIso.ofComponents`, with
`SmoothRep.mkIso` and `MixedProductTensor.smoothRep_hom_ext`, gives a natural
isomorphism onto `rightPsiPosTarget`.

`binaryNormalizedProductFunctor (r'+1) (k+1)` is by definition
`binaryPositiveProductFunctor`. Whiskering the inverse of
`generalLinearRankCastIso` replaces the pullback by the actual
`generalLinearRankCast`. This proves `rightPsiCompatibility_pos T k r'`, the
clause instance at `(k, r'+1)`. The theorem uses
`set_option maxHeartbeats 1000000`, a finite bound.

At `r = 0`, `rightPsiCompatibility_zero T k` from the helper gives the clause
instance at `(k, 0)`. It identifies both sides with `τ ⊗ ρ`, with `g` acting
by `1 ⊗ ρ(g)`. It keeps the entire `GL_0` carrier and both actual input maps.

Finally `rightPsiCompatibility` introduces `k, r` and splits `r` into zero
and successor. The result is exactly the published `Nonempty`
natural-isomorphism proposition for every pair of ranks, with independent
`uF` and `uV`.

## Generic lemmas of this module

These are internal and derived; each is a short Mathlib or Library argument.

- `compactOpenBasis_of_continuousMulEquiv` and
  `compactOpenCover_of_continuousMulEquiv`: compact open subgroup bases and
  covers transport along isomorphisms of topological groups.
- `compEquivOfEq`: restrictions along equal homomorphisms are equivalent
  through the identity.
- `compactInductionTwistEquiv_natural`: the published character-twist
  equivalence commutes with `compactInducedMap`.
- `chain_natural₄`: naturality of a composite of four maps.
- `psiMinusCoinvariantsEquiv` (with `_mk`, `_natural_quotient`, `_natural`),
  `rightPsiCastContinuous` (with `_toMonoidHom`), `mem_rightPsi_iff`,
  `rightPsi_transport_equivariant`, `rightPsiCompactEquivOf` (with
  `_natural`), `mirabolic_compactOpenBasis` and `rightPsiPosTarget`, as
  described above.

## Mathematical dependency and restriction audit

The direct imports are the helper
`Langlands.Representation.Derivative.MirabolicProductMinusRightPsiCoefficient`
and the published `Langlands.Representation.Induction.CharacterTwistProof`,
`Langlands.Representation.Derivative.MirabolicProductRestrictionTransport` and
`Langlands.Group.GL.CompactOpen`. Through the helpers it imports the
published `MirabolicProductMinusRightBoundary` and `BinaryPositiveCompact`.
The mathematical inputs are independently accepted and published. Integration
extracts the two existing elementary lemmas into shared lower modules,
preserving their proofs and statements. The target proposition remains unchanged. The table
covers the actual direct and transitive mathematical inputs and the host's
inherited exclusions. Proposition definitions in the closure supply types and
constructions; none is used as a proof of its conclusion.

| Condition | Actual dependency and scope |
| --- | --- |
| Concrete radical coinvariants | `splitStagesCompactEquiv` and `_natural` (published `SplitStagesComparison`, `SplitStagesRetraction`) are used with the actual groups and coefficient of the right mixed product. Their hypotheses (continuity, closedness, containments, smoothness, compact open bases, Borel and Haar data, quotient measure) are proved in this module and its helpers. No comparison or bijectivity premise is assumed. |
| Rank-one source | `trivialSplitKernelEquiv` and its laws (published `MirabolicProductMinusRightBoundary`, with `SplitKernelCharacter`) use the trivial intersection of the case (III) subgroup with the radical. The full `GL_0` carrier and both input maps are kept. |
| Haar ratio and normalization | The Haar ratio `|det D|` is computed from the published `mulEquivHaarChar_conj_levi_inv` and the kernel identifications. The proof keeps the actual `Ψ⁻` normalization, the case (III) character and the binary half modulus, and proves the exact real-power identity. No residual twist or Haar-scaling comparison is assumed. |
| Coefficient tensor quotient | The coefficient identification uses tensor and quotient universal properties, the explicit isomorphism `N ≅ V_(r+1)` and the published `splitStagesCoefficientEquiv`. No finiteness conclusion is used. |
| Positive binary induction | The published `binaryPositiveCompactEquiv` uses the binary tensor coefficient laws, compact-inclusion bijectivity and actual parabolic quotient compactness. `compactInducedTransport` (published `MirabolicProductRestrictionTransport`) is the generic transport of compact induction along a group isomorphism. Each is a published construction or proof. |
| Parabolic quotient compactness | The published proof obtains `G = P K` from the integral-subgroup Iwasawa decomposition and compactness of `K`, then applies continuity of the quotient map. Its Iwasawa input is proved by elementary column reduction. No representation finiteness or classification is used. |
| Unimodularity and quotient measures | `Haar.compactOpenCoverUnimodularity` (published proof of `CompactOpenCoverUnimodularityStatement`) and `QuotientIntegration.compatibleMeasureExists` are measure-theoretic results on locally compact groups. Compact averaging in the lower quotient-integral modules is unrelated to the prohibited arbitrary-character coinvariant-finiteness conclusions. |
| Restriction-sequence modules | `MirabolicProductRestrictionTransport` supplies only `compactInducedTransport`. `MirabolicProductRestrictionFactors` supplies only the binary tensor equivalence used by the bridge; its imports `MirabolicProductRestrictionOrbits` and `MinusVanishing` are incidental. No restriction-sequence conclusion (BZ77 4.13(a)) is used, and the separate restriction-sequence owner is not duplicated. |
| Shared published lemmas | The Groups helper imports `Langlands.GeneralLinear.determinant_blockParabolic` from `Group.GL.BlockDeterminant` and `Langlands.Geometric.haarChar_eq_of_conjugacy` from `HarmonicAnalysis.HaarConjugacy`. Their existing proofs were moved unchanged into these lower modules; they are matrix and measure facts and introduce no excluded input. |
| Full GL₀ boundary | At `r = 0` both actual carriers and maps remain. No positive input GL factor is replaced by `GL_0` or a unit object. |
| Naturality and ranks | The actual coefficient, compact-induction and product maps commute in both inputs. The final zero/successor assembly has exactly the proposition's ranks, functors and rank transport. No semisimplification, character identity or Grothendieck-group statement replaces the target. |
| Plus functors and adjunction | No plus-functor or adjunction theorem or module supplies an input. `Induction.StructuralStatement`, imported through `CharacterTwistProof`, supplies only proposition definitions, including `OpenSubgroupAdjunctionClause`. None of them is used as a proof; only the published character-twist construction `compactInductionTwistEquiv` is used. |
| BZ77 4.13(d) and general Leibniz | No submodule-detection conclusion, general Leibniz proof or derivative-filtration theorem is imported or used. `Filtration.Definitions` supplies definitions only. |
| Segment derivative and Jacquet formulas | No segment derivative formula, Ze80 §3.5 or §9.6, `SegmentFullJacquetFormula`, `SegmentHeadJacquetFormula`, `SegmentSocleJacquetFormula`, or `SegmentSpecialJacquetExponentNormFormula` supplies a direct or transitive input. |
| Individual segment existence | No individual special-head/reverse-socle or segment-socle/reverse-head existence conclusion, proof successor or downstream consequence is used. |
| Linked and unlinked socle consumers | `UnlinkedSegmentSocleProductIrreducible`, `LinkedSegmentSocleReverseProductStructure`, `LinkedSegmentSoclePairReducible`, `JuxtaposedSegmentSocleReverseProductStructure` and `LinkedSegmentSocleReverseProductQuotientHom` are absent from the proof dependencies. |
| Segment product and commutation consumers | No `SegmentSocleProductIrreducibility`, `AdjacentUnlinkedSegmentSocleSwap`, `TwoSegmentSocleCommutation`, `LinkedSegmentSocleGluing`, Ze80 4.2 or 9.7 criterion, or their successors or consequences is used. |
| Special-head criterion and uniqueness | `SegmentHeadProductIrreducibility` and `GenericSegmentProductUniqueness`, their parent tasks, successors and downstream consequences supply no input. |
| Ordered existence and multisegment exhaustion | No `OrderedMultisegmentSocleExistence`, `MultisegmentSocleExhaustion`, ordered strong-head existence, special-head multisegment exhaustion, quotient coverage or ordered-conversion conclusion is used. |
| Analytic, tempered and square-integrable classification | No analytic segment classification, `SegmentSpecialEssentialSquareIntegrability`, tempered uniqueness, `SquareIntegrableLanglandsClassification`, square-integrable or regular exhaustion, or Ze80 9.3 conclusion is used, including their proof successors and transitive consequences. |
| Two-supercuspidal consumers | Neither `TwoSupercuspidalNonadjacentProductIrreducible` nor `TwoSupercuspidalProductStructure`, their full-product assembly, successors or consequences is imported or used. |
| Supercuspidal and single-block finiteness | No `SupercuspidalCoinvariantFinitenessStatement`, all-character single-block conclusion or downstream consequence supplies an input. No arbitrary-character finiteness theorem is used. |
| Other Whittaker finiteness exclusions | `IrreducibleCoinvariantFinitenessStatement` and `LeviCuspidalCoinvariantFinitenessStatement`, their parent and proof tasks and their consequences are absent, as is the prohibited mirabolic finite-length route through that finiteness. |
| Whittaker and Rankin–Selberg modules in the closure | The Whittaker algebraic and GL modules provide character and coefficient definitions. Iwasawa provides the elementary group decomposition described above. The Rankin–Selberg imports contain lower measure, compact-orbit, cutoff and unimodularity constructions brought by the generic induction infrastructure. They supply no excluded finiteness, segment or classification input. |
| Other host clauses and pending results | The compatibility statement module supplies only the unchanged proposition and the functor definitions. The published `MirabolicProductMinusRightBoundary` is imported for its lower lemmas and its trivial-intersection split-kernel equivalence. Its clause theorem `rightPhiBoundary` is not used. The published left Psi modules and the left boundary module are not imported. No unproved left or right Phi comparison, short exact sequence, draft, pending candidate or consumer conclusion is used. |
| Parameters and run controls | The arbitrary supplied `T`, arbitrary smooth input carriers, zero objects and repeated factors are kept. No suspended or operator-paused worker supplies or waives a proof obligation. |

These rows cover every named task in the host's inherited union, its
mathematical conclusions, proof successors and downstream consequences. A
search over the source of the complete closure below and of this module found
no excluded declaration name and no task identifier in Lean code. The only
match of the word `Adjunction` is the proposition definition
`OpenSubgroupAdjunctionClause` noted above. The search also
found no `sorry`, `admit`, `native_decide` or new axiom. The entry theorem
depends only on Lean's standard `propext`, `Classical.choice` and
`Quot.sound`.

## Complete project import closure

The original review audited 187 transitive project imports at Library base
`3556873fa475ebf7c4932f5d037eb3dea71c4ddb`, including the three submitted
Zero, Groups and Coefficient helpers. Integration adds the two shared
lower modules described above. The final combined tree has 189
transitive project imports, excluding this module, computed from its actual
import lines. Mathlib dependencies come from the pinned supplied environment.

```text
Langlands.Analysis.Local.CompactOpenCoverUnimodularityProof
Langlands.Analysis.Local.CompactOpenCoverUnimodularityStatement
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
Langlands.Group.GL.BlockDeterminant
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
Langlands.Representation.Derivative.MinusVanishing
Langlands.Representation.Derivative.MirabolicCharacter
Langlands.Representation.Derivative.MirabolicLatticeBox
Langlands.Representation.Derivative.MirabolicMinus
Langlands.Representation.Derivative.MirabolicProductMinusCompatibilityStatement
Langlands.Representation.Derivative.MirabolicProductMinusRightBoundary
Langlands.Representation.Derivative.MirabolicProductMinusRightPsiCoefficient
Langlands.Representation.Derivative.MirabolicProductMinusRightPsiGroups
Langlands.Representation.Derivative.MirabolicProductMinusRightPsiZero
Langlands.Representation.Derivative.MirabolicProductRestrictionFactors
Langlands.Representation.Derivative.MirabolicProductRestrictionOrbits
Langlands.Representation.Derivative.MirabolicProductRestrictionTransport
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
Langlands.Representation.Induction.SplitKernelCharacter
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
