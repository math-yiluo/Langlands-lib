# The natural normalized left Psi compatibility

This module proves the unchanged published proposition
`Langlands.Derivative.MirabolicProductMinus.LeftPsiCompatibility.{uF,uV} F T`
from `MirabolicProductMinusCompatibilityStatement`. Its entry theorem is
`Langlands.Derivative.MirabolicProductMinus.leftPsiCompatibility`.
For every positive GL rank and every existing source mirabolic rank, it
constructs a natural isomorphism

```text
Ψ⁻(ρ × τ) ≅ ρ × Ψ⁻τ.
```

Both products and the minus functor are the actual published normalized
functors, with their actual maps. This focused proof establishes the left
Psi clause of BZ77 Proposition 4.13(b). The positive Phi comparisons and
the other clauses of the six-part host proposition are separate obligations.

## Original and derived provenance

The original is I. N. Bernstein and A. V. Zelevinsky, *Induced
representations of reductive p-adic groups I*, Ann. Sci. ENS (4) 10 (1977),
441–472; registered source `bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
Relevant passages are §1.8, printed pp.444–445 (PDF pp.5–6), for the
positive-half induction covariance and inverse-half localization action;
§§3.1–3.2, pp.450–451 (PDF pp.11–12), for the mirabolic radical and minus
functors; and §4.12, pp.456–458 (PDF pp.17–19), case (II), for the
left mixed product. Proposition 4.13(b), printed p.458 (PDF p.19), gives
the displayed compatibility, and the sentence after (d) requires all its
morphisms to be functorial. The source states the opposite orientation
of the isomorphism, which is equivalent by inversion. These passages and
their page images were read during the task; the complete p.458 image
was rechecked for this assembly. A bounded project/literature search
found no BZ77-specific erratum entry.

The proof route and its intermediate adapters are derived internal
content. The published `leftPsiInductionEquiv` computes the actual
normalized quotient as compact induction. This module identifies its
section subgroup and coefficient with the positive binary parabolic
model and applies the published `binaryPositiveCompactEquivOf`. Thus it
does not assume BZ77's compatibility or the general geometric lemma as
a theorem input. The new subgroup equality transport is ordinary
equality elimination.

## Parameters, ranks, carriers and functors

Fix arbitrary `{p : ℕ}`, `[Fact p.Prime]`, `F : PadicField.{uF} p` and
the supplied `T : F.TopologicalData`. All topologies and topological
group instances come from `T`. The input representation carrier
universe `uV` is independent of `uF`. The exact theorem has no additional
hypotheses.

The proposition quantifies `k,r : ℕ` and inputs
`ρ : SmoothRep ℂ (GL_(k+1)(F))` and
`τ : SmoothRep ℂ (mirabolic r F.Carrier)`.
Here `mirabolic r = P_(r+1)` and
`psiMinus T r : P_(r+1) → GL_r`.
The left mixed product has source group `P_((k+1)+r+1)`;
its Psi-minus is a representation of `GL_((k+1)+r)`.
Both sides have carrier universe `max uF uV`. The internal positive
construction writes the positive first rank as `k` rather than `k+1`
and assumes `hk : 0 < k`, `hr : 0 < r`; its final use substitutes
`k+1` for that `k`.

The source `r=0` case is `P₁ → GL₀`. Only the group `GL₀(F)` is
subsingleton: its smooth representations retain their entire arbitrary
vector-space carriers. No `P₀` is introduced. No Phi-minus is applied
to `P₁`; the conventional shift
`phiMinus T ψ r : P_(r+2) → P_(r+1)` is outside this focused Psi proof.
Zero objects, arbitrary smooth objects, and repeated factors are all
allowed. No admissibility, irreducibility, genericity, finite dimension,
finite length, chosen vector, chosen unit, or universe saturation is assumed.

## The positive-rank comparison

For internal positive `k,r`, set

```text
H = leftSubgroup k r F.Carrier ⊆ mirabolic (k+r) F.Carrier,
S = H.comap levi ⊆ GL_(k+r)(F),
B = BlockShape.binary k r hk hr,
P = B.parabolic F.Carrier.
```

The published helper proves `leftSubgroup_comap_levi_binary hk hr : S = P`.
Its `leftPsiCoefficientEquiv T X`, denoted `e_X`, is a linear equivalence
from the actual radical coinvariants of the mixed inducing coefficient to
`ρ ⊗ (psiMinus T r).obj τ`.
Write `κ_X = leftPsiNormalizedCoefficient T X`, the normalized section
coefficient on `S`. The same helper proves the exact action of `κ_X`,
the two section block projections, and the scalar half-modulus identity.
These retain the ambient inverse-half and source inverse-half normalizations.

`leftPsiBinaryCoefficient T hk hr X` pulls `κ_X` back along the inclusion
`P → S` supplied by the subgroup equality. For `q ∈ P`, its proved action is

```text
e_X(leftPsiBinaryCoefficient(q) z) =
  parabolicHalfModulus B q •
    (ρ(q₀) ⊗ (Ψ⁻τ)(q₁)) (e_X z),
```

where `q₀,q₁` are the two actual `B.leviProjection` blocks.
`leftPsiBinaryCoefficient_action` starts with the published normalized
coefficient action, identifies the two blocks by
`leftPsiSection_binary_projection` and `leftPsiSectionTwoBlock_projection`,
and identifies the scalar by `leftPsiSection_halfModulus`.
It transports the two block equalities through the tensor action using
`congrArg₂`, then transports that equality and the scalar equality through
scalar multiplication. In particular, no scalar or character is discarded.
Before the half-modulus identification, the helper's scalar is explicitly
`ν_k(q₀)^(r/2) ν_r(q₁)^(-k/2)`, the published positive binary half modulus.

The private `compactInducedSubgroupEqEquiv` transports compact induction
along any equality of subgroups, pulling the coefficient back along the
corresponding inclusion. Eliminating the equality reduces it to the
identity equivalence; its naturality proof reduces to reflexivity.

`leftPsiPositiveCompactEquiv` composes that transport from `S` to `P`
with `T.binaryPositiveCompactEquivOf`, instantiated with the actual
`leftPsiBinaryCoefficient`, `e_X`, and the proved action law.
The imported binary comparison transports the coefficient by the binary
tensor equivalence, then uses the compact inclusion into smooth induction.
The actual parabolic quotient is compact by the published
`Parabolic.parabolicQuotientCompact`, so this inclusion is bijective.
The resulting target is exactly the unchanged
`T.binaryPositiveProductFunctor hk hr`, not a replacement product.

`leftPsiPositiveEquiv` composes the published `leftPsiInductionEquiv T X`
with `leftPsiPositiveCompactEquiv`. Its source is the representation of
the actual `psiMinus T (k+r)` applied to the actual left mixed product.
The imported first equivalence was constructed from the ordinary
coinvariant comparison, the normal-split compact-induction comparison
and the character-twist comparison. Its concrete radical projection,
surjectivity, subgroup containment, kernel identity, continuity,
closedness and coefficient smoothness hypotheses were proved in that
published helper. No such hypothesis remains a premise here.

## Naturality and the exact proposition

For an arbitrary pair morphism `f=(f₁,f₂)`, the actual map
`leftPsiNormalizedCoefficientMap T X f` descends the tensor of the
two input maps to radical coinvariants and then restricts and twists it.
`leftPsiBinaryCoefficientMap` restricts it to `P`.
`leftPsiBinaryCoefficient_natural` is the published coefficient naturality
law after that restriction:

```text
e_Y ∘ coefficientMap(f) = (f₁ ⊗ Ψ⁻(f₂)) ∘ e_X.
```

`leftPsiPositiveCompactEquiv_natural` first uses naturality of the
subgroup equality transport, then
`binaryPositiveCompactEquivOf_natural` with exactly this coefficient
map and equality. `leftPsiPositiveEquiv_natural` composes it with
`leftPsiInductionEquiv_natural`. Thus the comparison commutes with
the Psi of the actual mixed-product map and the actual binary-product
map in both inputs.

For `r=0`, the published `leftPsiZeroEquiv` already targets the actual
`binaryNormalizedProductFunctor k 0`. It evaluates compact induction
from the whole section subgroup and identifies its coefficient with
`ρ ⊗ Ψ⁻τ`, then applies the inverse of the binary right-zero tensor
equivalence. Its proof uses subsingleton elimination only for GL₀
group elements. `leftPsiZeroEquiv_natural` retains both full input maps.

Finally `leftPsiCompatibility` introduces the proposition's `k,r`
and splits `r` into zero and successor. The zero branch uses the
published full-carrier comparison and naturality. In the successor
branch, the positive binary product is definitionally the
successor/successor `binaryNormalizedProductFunctor`; the ranks are
explicitly instantiated as `k+1` and `r+1`. In each branch
`SmoothRep.mkIso` turns the equivariant linear equivalence into an
isomorphism, and `NatIso.ofComponents` uses the proved naturality.
Equality of category morphisms follows from
`MixedProductTensor.smoothRep_hom_ext`. The result is precisely the
published `Nonempty` natural-isomorphism proposition for every pair
of ranks, with independent `uF,uV`.

## Mathematical dependency and restriction audit

The two direct imports are
`Langlands.Representation.Derivative.MirabolicProductMinusLeftPsiInduction`
and `Langlands.Representation.Induction.BinaryPositiveCompact`.
Both are independently accepted and published constructions with proved
equivariance and naturality laws. The target proposition and every
imported Lean/Markdown pair remain unchanged. The table covers actual
direct and transitive mathematical inputs, as well as the host's inherited
exclusions. Proposition definitions in the closure supply types and
constructions; they are never used as proofs of their conclusions.

| Condition | Actual dependency and scope |
| --- | --- |
| Concrete mixed-product localization | `leftPsiInductionEquiv` and its naturality specialize the published normal-coinvariant, normal-split and character-twist comparisons to the actual left mixed product. The radical projection and all topological and smoothness hypotheses are discharged in the helper. |
| Coefficient tensor quotient | The helper uses tensor and quotient universal properties and a proved surjective projection onto the source radical, followed by the published trivial-character localization equivalence. It uses no finiteness conclusion. |
| Determinant normalization | The helper proves matrix determinant factorization and the explicit real-power identity. This module retains both projected blocks and identifies the entire scalar with `parabolicHalfModulus`; there is no residual assumed twist or Haar-scaling comparison. |
| Positive binary induction | `binaryPositiveCompactEquivOf` uses the actual binary tensor coefficient laws, pointwise transport of compact induction, compact-inclusion bijectivity and actual parabolic quotient compactness. Each is a published lower construction or proof. |
| Parabolic quotient compactness | The published proof obtains `G=P K` from the integral-subgroup Iwasawa decomposition and compactness of `K`, then applies continuity of the quotient map. Its Iwasawa input is proved by elementary column reduction. No representation finiteness or classification is used. |
| Normal-coinvariant lower proofs | Published quotient relation-kernel, compact-induction surjectivity, local section, cutoff and compact averaging arguments supply the lower comparison. Compact averaging is unrelated to the prohibited arbitrary-character coinvariant-finiteness conclusions. |
| Binary tensor helper import | `MirabolicProductRestrictionFactors` supplies only `FiniteTensor.binaryLinearEquiv`, its external action law and its external-map law to the binary comparison. No restriction-sequence conclusion is used. Its orbit-helper and `MinusVanishing` imports are incidental to these tensor laws. |
| Imported stages infrastructure | The binary comparison uses only `Induction.compactInducedEquiv` from `SplitStagesComparison`, the pointwise coefficient-equivalence transport. Its broader split-kernel, Haar integral and stages imports are included in the complete closure below; no assumed stages comparison or derivative consumer is used here. |
| Full GL₀ boundary | `leftPsiZeroEquiv` uses whole-subgroup evaluation and the published binary right-zero tensor equivalence. Both actual carriers and maps remain. No positive input GL factor is replaced by GL₀ or a unit object. |
| Naturality and ranks | Actual coefficient, compact-induction and product maps commute in both inputs. The final zero/successor assembly has precisely the proposition's ranks and functors; no semisimplification, character identity or Grothendieck-group statement replaces the target. |
| Plus functors and adjunction | No plus-functor or adjunction theorem or module supplies an input. Matrix subgroups, including `plusSubgroup` where present in lower matrix definitions, do not assert a plus-functor result. |
| BZ77 4.13(d) and general Leibniz | No submodule-detection conclusion, general Leibniz proof or derivative-filtration theorem is imported or used. `Filtration.Definitions` supplies definitions only. |
| Segment derivative and Jacquet formulas | No segment derivative formula, Ze80 §3.5 or §9.6, `SegmentFullJacquetFormula`, `SegmentHeadJacquetFormula`, `SegmentSocleJacquetFormula`, or `SegmentSpecialJacquetExponentNormFormula` supplies a direct or transitive input. |
| Individual segment existence | No individual special-head/reverse-socle or segment-socle/reverse-head existence conclusion, proof successor or downstream consequence is used. |
| Linked and unlinked socle consumers | `UnlinkedSegmentSocleProductIrreducible`, `LinkedSegmentSocleReverseProductStructure`, `LinkedSegmentSoclePairReducible`, `JuxtaposedSegmentSocleReverseProductStructure`, and `LinkedSegmentSocleReverseProductQuotientHom` are absent from the proof dependencies. |
| Segment product and commutation consumers | No `SegmentSocleProductIrreducibility`, `AdjacentUnlinkedSegmentSocleSwap`, `TwoSegmentSocleCommutation`, `LinkedSegmentSocleGluing`, Ze80 4.2 or 9.7 criterion, or their successors or consequences is used. |
| Special-head criterion and uniqueness | `SegmentHeadProductIrreducibility` and `GenericSegmentProductUniqueness`, their parent tasks, successors and downstream consequences supply no input. |
| Ordered existence and multisegment exhaustion | No `OrderedMultisegmentSocleExistence`, `MultisegmentSocleExhaustion`, ordered strong-head existence, special-head multisegment exhaustion, quotient coverage or ordered-conversion conclusion is used. |
| Analytic, tempered and square-integrable classification | No analytic segment classification, `SegmentSpecialEssentialSquareIntegrability`, tempered uniqueness, `SquareIntegrableLanglandsClassification`, square-integrable or regular exhaustion, or Ze80 9.3 conclusion is used. This includes their proof successors and transitive consequences. |
| Two-supercuspidal consumers | Neither `TwoSupercuspidalNonadjacentProductIrreducible` nor `TwoSupercuspidalProductStructure`, their full-product assembly, successors or consequences is imported or used. |
| Supercuspidal and single-block finiteness | No `SupercuspidalCoinvariantFinitenessStatement`, all-character single-block conclusion or downstream consequence supplies an input. No arbitrary-character finiteness theorem is used. |
| Other Whittaker finiteness exclusions | `IrreducibleCoinvariantFinitenessStatement` and `LeviCuspidalCoinvariantFinitenessStatement`, their parent/proof tasks and consequences are absent, as is the prohibited mirabolic finite-length route through that finiteness. |
| Whittaker and Rankin–Selberg modules in the closure | Whittaker algebraic/GL modules provide character and coefficient definitions; Iwasawa provides the elementary group decomposition described above. The Rankin–Selberg imports contain lower measure, compact-orbit, cutoff and unimodularity constructions brought by generic induction infrastructure. They do not supply any excluded finiteness, segment or classification input. |
| Other host clauses and pending results | The compatibility statement module supplies only the unchanged proposition and functor definitions. No unproved left/right Phi comparison, short exact sequence, right Psi comparison, draft, pending candidate or consumer conclusion is used. |
| Parameters and run controls | Arbitrary supplied `T`, arbitrary smooth input carriers, zero objects and repeated factors are retained. No suspended or operator-paused worker is used to supply or waive a proof obligation. Shared ownership does not grant a mathematical premise. |

The exclusions in these rows include all named tasks in the host's inherited
union, their mathematical conclusions, proof successors and downstream
consequences. Searches over the entire project source closure found no
excluded consumer declaration or task identifier in Lean code and no
proof holes or new axioms. The actual lower proof bodies and their
published dependency explanations support the mathematical audit above.
Only Lean's standard `propext`, `Classical.choice` and `Quot.sound`
are required by the complete entry theorem.

## Complete project import closure

There are exactly 174 transitive project imports, excluding this module
itself, at the audited Library base
`2003a7a6a41b5e54c3f790e0887743ed616ed614`.
The list below is computed from the actual two imports, including both
direct roots. Every listed Lean/Markdown pair was byte-compared against
that Library and its published manifest. All agree. Mathlib dependencies
come from the pinned supplied Lean environment.


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
Langlands.Representation.Derivative.MinusVanishing
Langlands.Representation.Derivative.MirabolicCharacter
Langlands.Representation.Derivative.MirabolicLatticeBox
Langlands.Representation.Derivative.MirabolicMinus
Langlands.Representation.Derivative.MirabolicProductMinusCompatibilityStatement
Langlands.Representation.Derivative.MirabolicProductMinusLeftPsiInduction
Langlands.Representation.Derivative.MirabolicProductRestrictionFactors
Langlands.Representation.Derivative.MirabolicProductRestrictionOrbits
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
