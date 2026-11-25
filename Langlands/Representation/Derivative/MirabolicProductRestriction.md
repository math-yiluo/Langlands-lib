# Restriction of a binary product to the mirabolic subgroup: proof

This module proves the published proposition
`Langlands.Derivative.MirabolicProductRestrictionStatement.{uF,uV} F T` of
module `Langlands.Representation.Derivative.MirabolicProductRestrictionStatement`
(Bernstein–Zelevinsky 1977, Proposition 4.13(a), for all positive ranks), as

```lean
theorem Langlands.Derivative.mirabolicProductRestriction {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) :
    MirabolicProductRestrictionStatement.{uF, uV} F T
```

with independent universes `uF, uV` and no further hypotheses. The statement's
Lean/Markdown pair and every module it imports are unchanged.

## What is proved

For all `m n : ℕ` (ranks `a = m+1`, `b = n+1`) the proof constructs actual
natural transformations

- `i : restrictionSubobject T m n ⟶ restrictedProduct T m n` and
- `q : restrictedProduct T m n ⟶ restrictionQuotient T m n`

between the published helper functors on pairs `(A, B)` of arbitrary smooth
complex representations of `GL_(m+1)(F)` and `GL_(n+1)(F)`, valued in
`SmoothRep.{0,uF,max uF uV} ℂ (mirabolic (m+n+1) F.Carrier)`, i.e. `P_(a+b)`,
and proves at every pair that `SmoothRep.hom (i.app X)` is injective, its range
equals the kernel of `SmoothRep.hom (q.app X)`, and `SmoothRep.hom (q.app X)` is
surjective. The first term is the published right mixed product of case (III)
of `(A|P_a, B)`, including the factor `ε` already in `rightMixedProductFunctor`;
the last term is the published left mixed product of case (II) of
`(A, B|P_b)`; the middle term is the published binary normalized product
restricted to `P_(a+b)`. All rank transports of the helper functors are kept, on
objects and maps. No admissibility, irreducibility, finiteness, genericity,
chosen vector, canonical topology or theorem-valued premise is used; zero
objects and repeated factors are covered since nothing is assumed of `(A, B)`.

## Source orientation

Bernstein–Zelevinsky, *Induced representations of reductive p-adic groups I*,
Ann. Sci. ENS (4) 10 (1977), source ID `bernstein-zelevinsky-1977-induced-i`,
SHA256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
Proposition 4.13(a) is on printed p.458 (PDF page 19) and its proof is §7.1 on
printed p.471 (PDF page 32), which was read for this proof: the restriction of
`ρ × σ` to `P` is computed by Theorem 5.2 with two `Q`-orbits on `P \ G`, the
closed orbit of `P e` and the open orbit of `P w⁻¹` for a permutation matrix
`w`, giving the quotient `ρ × (σ|P)` and the subrepresentation `(ρ|P) × σ`,
with the characters compared via §6.5. The Lean proof follows this route, using
the published Lean version of Theorem 5.2 for trivial localization data
(`Langlands.Geometric.closedSubgroupMackeyFiltration`), an explicit Lean
permutation representative (not the source's cyclic permutation), and direct
character computations in place of §6.5 and §6.1.

## The implemented proof

Throughout, `N = (m+1)+(n+1)`, which is definitionally `((m+1)+n)+1`, `P` is the
published upper block parabolic of the binary shape `(m+1, n+1)` in `GL_N(F)`
and `Q` is the published mirabolic subgroup `mirabolic ((m+1)+n)` of the same
group.

1. **Rank casts** (module `MirabolicProductRestrictionCasts`). The three helper
   functors are rewritten (`restrictedProduct_eq`, `restrictionSubobject_eq`,
   `restrictionQuotient_eq`) as functors to `P_((m+1)+n+1) = Q` followed by the
   common published `mirabolicRankCast` along `(m+1)+n = m+n+1`. In the first
   term the published cast along `(n+1)+m = m+n+1` is split into a cast to
   `(m+1)+n` followed by that common cast, and the first cast is replaced by the
   equal pullback functor along `mirabolicCast` (`mirabolicRankCast_eq_pullback`).
   `exists_exact_comp_mirabolicRankCast` transports the exactness data through
   the common cast. What remains is `core`, the sequence on `Q`.
2. **Orbits** (module `MirabolicProductRestrictionOrbits`). `orbitOrdering`
   is the published `OrderedDoubleCosets P Q 2` with representatives
   `openRep` (open orbit, first) and `1` (closed orbit, second); the closed
   orbit is where the last row of `g⁻¹` vanishes on the first block.
3. **Mackey sequence** (module `MirabolicProductRestrictionMackey`).
   `exists_exact_restrictedCompactInduction` applies the published
   `closedSubgroupMackeyFiltration` to `orbitOrdering` and the general
   `RepFunctorFiltration.exists_exact_of_two`, giving natural maps
   `ic : orbitPiece P Q w ⟶ restrictedCompactInduction P Q` and
   `qc : restrictedCompactInduction P Q ⟶ orbitPiece P Q 1` that are injective,
   exact in the middle and surjective at every smooth representation of `P`.
4. **Inducing data.** `leviInducingFunctor` inflates a smooth representation of
   the binary Levi along the published Levi projection and twists it by the
   inflated published `T.leviHalfCharacter`; `inducingFunctor` is the published
   `binaryPairFamilyFunctor`, the published `FiniteTensor.externalFunctor` and
   `leviInducingFunctor`, so `(inducingFunctor T m n).obj (A, B)` is exactly the
   inducing representation `δ_P^(1/2) (A ⊠ B)` of the published binary product.
5. **Middle term.** `midEquiv` identifies compact induction from `P` restricted
   to `Q` with the restricted binary product by the published canonical
   inclusion `Induction.compactInclusion`, bijective by the published
   `compactInclusion_bijective_of_compactSpace` because `P \ GL_N` is compact
   (published `Parabolic.parabolicQuotientCompact`). The binary product is
   definitionally smooth induction of the inducing data
   (`midFunctor_obj_representation`).
6. **Closed orbit.** `quotEquiv` identifies the published left mixed product
   `leftMixedProductFunctor (m+1) n` of `(A, B|P_b)` with `orbitPiece P Q 1` by
   the transport lemma `Induction.compactInducedTransport` of module
   `MirabolicProductRestrictionTransport`, with the identity of `Q`, the
   stabilizer identification `mem_closedStabilizer_iff` (module
   `MirabolicProductRestrictionStabilizers`) and the coefficient equivalence
   `tensorEquiv = FiniteTensor.binaryLinearEquiv` from the block tensor to
   `A ⊗ B` (module `MirabolicProductRestrictionFactors`). The coefficient
   condition `quot_hE` uses `closedStabilizer_levi_zero/one` and
   `leviHalfModulus_eq_leftLeviCharacter`: on the stabilizer, `δ_P^(1/2)` is
   the published case (II) character `χ_L`.
7. **Open orbit.** `subEquiv` identifies the pullback along `openCast` of the
   published right mixed product `rightMixedProductFunctor (n+1) m` of
   `(A|P_a, B)` with `orbitPiece P Q w` by the same transport lemma with
   `φ = openCast`, the identification `mem_openStabilizer_iff`, and the same
   `tensorEquiv`; the coefficient condition `sub_hE` uses
   `openStabilizer_levi_zero/one` and `leviHalfModulus_eq_rightLeviCharacter`:
   on the stabilizer, `δ_P^(1/2)` is the published case (III) character `χ_R`,
   which already contains the retained factor `ε`.
8. **Naturality.** `subEquiv_naturality` and `quotEquiv_naturality` follow from
   the naturality statement `compactInducedTransport_natural` with
   `pair_hT` (the tensor identification commutes with `f ⊗ g`), and
   `midEquiv_naturality` holds by definition.
9. **Assembly** (`core`). The component of `i` at `X` is
   `midEquiv X ∘ ic ∘ subEquiv X` and that of `q` is
   `(quotEquiv X)⁻¹ ∘ qc ∘ (midEquiv X)⁻¹`; naturality of `i` and `q` follows from
   steps 3 and 8, and the three exactness properties transfer along the linear
   equivalences (`exact_of_linearEquiv`). The final theorem
   `mirabolicProductRestriction` rewrites the statement with step 1 and applies
   `exists_exact_comp_mirabolicRankCast` to `core`.

The maps are the natural ones of the source: `i` is extension of functions from
the open orbit, transported to the right mixed product, and `q` is restriction
of functions to the closed orbit, transported to the left mixed product.

## Import closure

The direct project imports of this module are
`Derivative.MirabolicProductRestrictionMackey`,
`Derivative.MirabolicProductRestrictionStabilizers`,
`Derivative.MirabolicProductRestrictionFactors`,
`Derivative.MirabolicProductRestrictionTransport`,
`Induction.CompactQuotientProof`, `Parabolic.QuotientCompactProof`,
`Twist.SmoothProof` and `Smooth.Transfer.PullbackProof` (all under
`Langlands.Representation`). The complete recursively read project import
closure, excluding this module and Mathlib, has 159 modules:

New helper modules of this proof (6):

```text
Langlands.Representation.Derivative.MirabolicProductRestrictionCasts
Langlands.Representation.Derivative.MirabolicProductRestrictionFactors
Langlands.Representation.Derivative.MirabolicProductRestrictionMackey
Langlands.Representation.Derivative.MirabolicProductRestrictionOrbits
Langlands.Representation.Derivative.MirabolicProductRestrictionStabilizers
Langlands.Representation.Derivative.MirabolicProductRestrictionTransport
```

The published statement module and its recursive project imports (74):

```text
Langlands.Group.GL.Basic
Langlands.Group.GL.BlockModulus
Langlands.Group.GL.Blocks
Langlands.Group.GL.Mirabolic
Langlands.Group.GL.MirabolicMixedProductSubgroups
Langlands.Group.GL.MirabolicOppositeIntersection
Langlands.Group.GL.MirabolicProjection
Langlands.Group.GL.MirabolicRadical
Langlands.Group.GL.Nonarchimedean
Langlands.Group.GL.NonarchimedeanStatement
Langlands.Group.GL.NormalizedCharacter
Langlands.Group.GL.OppositeBlocks
Langlands.Group.GL.Padic
Langlands.Group.GL.PadicBlocks
Langlands.Group.GL.RankMaps
Langlands.Group.GL.RankReindex
Langlands.Group.GL.UpperUnipotent
Langlands.HarmonicAnalysis.Basic
Langlands.LocalField.Canonical
Langlands.LocalField.Definitions
Langlands.LocalField.Normalization.Definitions
Langlands.LocalField.Normalization.Proof
Langlands.LocalField.Normalization.Statement
Langlands.LocalField.Topology
Langlands.Representation.Category.Basic
Langlands.Representation.Category.Subquotients
Langlands.Representation.Category.Twist
Langlands.Representation.Derivative.Homogeneity
Langlands.Representation.Derivative.Iteration
Langlands.Representation.Derivative.MirabolicCharacter
Langlands.Representation.Derivative.MirabolicMinus
Langlands.Representation.Derivative.MirabolicProductRestrictionStatement
Langlands.Representation.Dual.Definitions
Langlands.Representation.Induction.BinaryProduct
Langlands.Representation.Induction.BlockFactors
Langlands.Representation.Induction.Definitions
Langlands.Representation.Induction.Parabolic
Langlands.Representation.Jacquet.Coinvariants
Langlands.Representation.Jacquet.Localization
Langlands.Representation.Jacquet.PositiveCharacter
Langlands.Representation.Jacquet.SmoothTwist
Langlands.Representation.MatrixCoefficient.Definitions
Langlands.Representation.MatrixCoefficient.LawsProof
Langlands.Representation.MatrixCoefficient.LawsStatement
Langlands.Representation.Mirabolic.MixedProducts
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
Langlands.Topology.CompactNormCharacter
Langlands.Topology.Nonarchimedean.Subgroup
```

Further published project modules imported by the proof (53):

```text
Langlands.Analysis.Local.QuotientMeasure
Langlands.Analysis.Local.QuotientTopology
Langlands.Group.GL.CompactOpen
Langlands.Group.GL.CountabilityProof
Langlands.Group.GL.CountabilityStatement
Langlands.Group.GL.Maps
Langlands.Group.GL.PadicOppositeBlocks
Langlands.Group.GL.PadicUpperUnipotent
Langlands.Group.GL.TriangularParabolic
Langlands.HarmonicAnalysis.PadicHaarScalingStatement
Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof
Langlands.Representation.Classification.Supercuspidal
Langlands.Representation.Classification.SupercuspidalContragredientAux
Langlands.Representation.Classification.SupercuspidalContragredientStatement
Langlands.Representation.Compact.Definitions
Langlands.Representation.Compact.FiniteMean
Langlands.Representation.Conductor.Congruence
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
Langlands.Representation.Induction.CompactLocalSection
Langlands.Representation.Induction.CompactQuotientCutoff
Langlands.Representation.Induction.CompactQuotientProof
Langlands.Representation.Induction.StructuralStatement
Langlands.Representation.OrbitSpan
Langlands.Representation.Parabolic.GeometricPrerequisitesStatement
Langlands.Representation.Parabolic.QuotientCompactProof
Langlands.Representation.Smooth.Admissibility.EquivalenceProof
Langlands.Representation.Smooth.Admissibility.EquivalenceStatement
Langlands.Representation.Smooth.Contragredient.CompactDualityProof
Langlands.Representation.Smooth.Contragredient.CompactDualityStatement
Langlands.Representation.Smooth.Contragredient.Definitions
Langlands.Representation.Smooth.Contragredient.FixedVectorsDefinitions
Langlands.Representation.Smooth.Contragredient.LawsProof
Langlands.Representation.Smooth.Contragredient.LawsStatement
Langlands.Representation.Smooth.FixedVectors.Definitions
Langlands.Representation.Smooth.SmallRealizationProof
Langlands.Representation.Smooth.SmallRealizationStatement
Langlands.Representation.Smooth.SmoothPart.FixedVectorsDefinitions
Langlands.Representation.Tensor.FiniteEquivalences
Langlands.Representation.Unitary.Basic
Langlands.Representation.Whittaker.Iwasawa
Langlands.Topology.CompactOpen.NeighborhoodBasis
Langlands.Topology.CompactOpen.NeighborhoodBasisStatement
```

Published project modules reached only through the helper imports
`Derivative.MinusVanishing` (from `MirabolicProductRestrictionOrbits`) and
`Group.GL.MirabolicModularCharacterProof` (from
`MirabolicProductRestrictionFactors`), including these two modules (26):

```text
Langlands.Analysis.Local.ModularCompactAverage
Langlands.Group.GL.MirabolicModularCharacterProof
Langlands.Group.GL.MirabolicModularCharacterStatement
Langlands.Group.GL.MirabolicModulusProof
Langlands.Group.GL.MirabolicModulusStatement
Langlands.Group.HaarModulus
Langlands.HarmonicAnalysis.Conductor
Langlands.HarmonicAnalysis.PadicAdditiveConductorProof
Langlands.HarmonicAnalysis.PadicLatticeTopology
Langlands.HarmonicAnalysis.PadicRectangularHaarScalingProof
Langlands.LocalFactor.Harmonic.Statement
Langlands.Representation.Compact.OrbitMeanTranslation
Langlands.Representation.Compact.ProjectionProof
Langlands.Representation.Compact.ProjectionStatement
Langlands.Representation.Derivative.MinusVanishing
Langlands.Representation.Derivative.MirabolicLatticeBox
Langlands.Representation.Jacquet.CharacterAveraging
Langlands.Representation.RankinSelberg.GeneralLinearUnimodularity
Langlands.Representation.RankinSelberg.LastRowCompactOrbitProof
Langlands.Representation.RankinSelberg.LastRowCompactOrbitStatement
Langlands.Representation.RankinSelberg.Measures
Langlands.Representation.RankinSelberg.QuotientIntegrals
Langlands.Representation.RankinSelberg.UnimodularityStatement
Langlands.Representation.RankinSelberg.ZeroRowLastRowCutoffProof
Langlands.Representation.RankinSelberg.ZeroRowLastRowCutoffStatement
Langlands.Topology.CompactOpen.ConjugationStabilizer
```

## Mathematical proof dependencies

The published results used as proved inputs, with their modules, are:

- `Geometric.closedSubgroupMackeyFiltration` (`Geometric.ClosedSubgroupMackeyProof`),
  whose own proof uses the published `closedOrbitSectionExtension`
  (`Geometric.OrbitSectionExtensionProof`), `cosetOrbitHomeomorph`
  (`Geometric.CosetOrbitHomeomorph`), the support-step restriction of
  `Geometric.CompactOrbitRestriction`/`OrbitRestriction`, and
  `Filtration.QuotientFirstIso`; this is the published Lean form of BZ77
  Theorem 5.2 for trivial localization data.
- `Parabolic.parabolicQuotientCompact` (`Parabolic.QuotientCompactProof`, by the
  Iwasawa decomposition of `Whittaker.Iwasawa` and `Group.GL.TriangularParabolic`)
  and `Induction.compactInclusion_bijective_of_compactSpace`
  (`Induction.CompactQuotientProof`).
- The topological facts `T.generalLinearNonarchimedean` (`Group.GL.CompactOpen`),
  `T.generalLinearSigmaCompactSpace` (`Group.GL.CountabilityProof`, via
  `Smooth.SmallRealizationProof` for second countability),
  `T.generalLinearLocallyCompactSpace`, `T.generalLinearT2Space`,
  `T.generalLinearTopologicalGroup` (`Group.GL.Padic`), `T.fieldT2`
  (`LocalField.Topology`), `BlockShape.isClosed_parabolic` (`Group.GL.Blocks`)
  and `Mirabolic.isClosed` (`Group.GL.Mirabolic`).
- `isSmooth_twist_iff` (`Twist.SmoothProof`) and `isSmooth_comp`
  (`Smooth.Transfer.PullbackProof`).
- Elementary published lemmas about the constructions: permutation matrices
  (`Group.GL.Maps`), the binary shape and block parabolics
  (`Group.GL.Blocks`, `Group.GL.MirabolicOppositeIntersection`), the case (II)
  and (III) subgroups, coordinates and projections
  (`Group.GL.MirabolicMixedProductSubgroups`), the block modulus
  (`Group.GL.BlockModulus`), the mixed-product characters
  (`Mirabolic.MixedProducts`), the tensor splitting
  `FiniteTensor.headTailLinearEquiv` (`Tensor.FiniteEquivalences`) and the
  filtration API (`Filtration.Definitions`, `Filtration.QuotientFirstIso`).
- Two elementary matrix lemmas: `Langlands.Derivative.Mirabolic.exists_lastRow_eq_of_ne_zero`
  (`Derivative.MinusVanishing`), used in `MirabolicProductRestrictionOrbits`,
  and `Langlands.GeneralLinear.Mirabolic.determinant_projection`
  (`Group.GL.MirabolicModularCharacterProof`), used in
  `MirabolicProductRestrictionFactors`. Their own proofs use only Mathlib
  linear algebra: the first replaces a row of the identity matrix and permutes
  rows (`Matrix.det_updateRow_sum`, `Matrix.det_permute`); the second is a
  Laplace expansion along the last row through the private `det_lastRow`
  (`Matrix.det_succ_row`). No other declaration of these two modules, and none
  of the further modules they import, is used.

No published proposition definition is used as a hypothesis, and no unproved
statement is used.

## Independence audit

Every proved input above lies in the import closure listed, so its direct and
transitive proof dependencies lie there too. The closure was checked module by
module against each of the exclusions below.

- **Segment and multisegment consumer statements.** The closure contains no
  module stating or proving `UnlinkedSegmentSocleProductIrreducible`,
  `LinkedSegmentSocleReverseProductStructure`, `LinkedSegmentSoclePairReducible`,
  `JuxtaposedSegmentSocleReverseProductStructure`,
  `LinkedSegmentSocleReverseProductQuotientHom`,
  `SegmentSocleProductIrreducibility`, `AdjacentUnlinkedSegmentSocleSwap`,
  `TwoSegmentSocleCommutation`, `LinkedSegmentSocleGluing`,
  `OrderedMultisegmentSocleExistence`, `MultisegmentSocleExhaustion`,
  `SegmentHeadProductIrreducibility`, `GenericSegmentProductUniqueness`,
  `SquareIntegrableLanglandsClassification`,
  `SegmentSpecialEssentialSquareIntegrability`, `SegmentFullJacquetFormula`,
  `SegmentHeadJacquetFormula`, `SegmentSocleJacquetFormula` or
  `SegmentSpecialJacquetExponentNormFormula`. The strings `Segment`, `Socle`,
  `Multisegment`, `SquareIntegrable`, `Tempered`, `TwoSupercuspidal`,
  `CoinvariantFiniteness` and `Leibniz` occur in no source of the closure; the
  only occurrences of `Exhaustion` are `UnipotentExhaustionClause` of
  `Parabolic.GeometricPrerequisitesStatement` and the section `Exhaustion` of
  `Jacquet.CharacterAveraging` (compact-open exhaustions of a unipotent group,
  not classification exhaustions, and not used). Hence the proof is independent of these
  results, of the analytic segment classification
  (`SegmentEssentialSquareIntegrableClassification`), the special-head
  multisegment exhaustion (`MultisegmentHeadExhaustion`), the ordered head
  existence (`OrderedMultisegmentHeadExistence`), the quotient coverage
  (`OrderedMultisegmentQuotientExhaustion`), the ordered special-segment
  conversion (`OrderedSegmentSquareIntegrableConversion`), tempered block
  uniqueness (`TemperedBlockUniqueness`), square-integrable exhaustion
  (`SquareIntegrableLanglandsExhaustion`), regular exhaustion
  (`GLRegularLanglandsExhaustionStatement`) and the individual
  special-head/reverse-socle and segment-socle/reverse-head existence results,
  and of their conclusions and proofs.
- **Two-supercuspidal arguments.** No module states or proves
  `TwoSupercuspidalNonadjacentProductIrreducible` or
  `TwoSupercuspidalProductStructure`, and neither result is used.
- **Derivative results.** No derivative formula, exactness or Leibniz result is
  used. The closure contains the definition modules `Derivative.MirabolicMinus`,
  `Derivative.MirabolicCharacter`, `Derivative.Iteration` and
  `Derivative.Homogeneity` from the statement's closure, and of these only the
  definitions `generalLinearRestriction`, `generalLinearRankCast` and
  `mirabolicRankCast` are used. The closure also contains the published
  `Derivative.MinusVanishing` and its elementary helper
  `Derivative.MirabolicLatticeBox`. `MinusVanishing` proves
  `subsingleton_of_psiMinus_phiMinus`, the vanishing consequence of BZ77
  Proposition 3.2(e) (a representation of a mirabolic group with `Ψ⁻ = 0` and
  `Φ⁻ = 0` is zero). It is a published proof, not a 4.13 or 4.14
  result, and it does not import this proof's statement. This proof uses
  neither that theorem nor any other declaration of `MinusVanishing` except the
  elementary matrix lemma `exists_lastRow_eq_of_ne_zero`. The closure contains
  no module stating or proving a derivative exactness, Leibniz filtration,
  minus compatibility, 4.13(b–d) or 4.14 result (the only exactness
  proposition in the closure is the unused induction clause
  `InductionExactnessClause` of `Induction.StructuralStatement`); in
  particular no mirabolic minus exactness result is used.
- **Ze80.** No segment derivative formula (Ze80 §3.5, §9.6), segment
  irreducibility criterion (Ze80 4.2, 9.7), square-integrability result
  (Ze80 9.3), classification or exhaustion theorem occurs in the closure.
- **Whittaker finiteness.** The closure contains no
  `Langlands.Whittaker.IrreducibleCoinvariantFinitenessStatement`,
  `LeviCuspidalCoinvariantFinitenessStatement` or
  `Langlands.Whittaker.SupercuspidalCoinvariantFinitenessStatement`, nor any
  module proving them, the all-character single-block conclusion or mirabolic
  finite length through that finiteness. The
  Whittaker modules in the closure are `Whittaker.Algebraic` and
  `Whittaker.GeneralLinear` (algebraic character infrastructure, already in the
  statement's closure) and `Whittaker.Iwasawa` (the Iwasawa decomposition used
  for compactness of `P \ GL_N`). The Rankin–Selberg modules reached through
  `Derivative.MinusVanishing` and `Group.GL.MirabolicModularCharacterProof`
  concern Haar measures, quotient integrals, the compact orbit of the last
  row and a compact last-row cutoff for Whittaker coefficients
  (`RankinSelberg.ZeroRowLastRowCutoffProof`). They state or prove no
  coinvariant finiteness, finite-length or classification result, and none of
  their declarations is used by this proof.
- **Classification modules.** The only `Classification` modules in the closure
  are `Classification.Supercuspidal` (the definition of supercuspidality),
  `Classification.SupercuspidalContragredientStatement` and
  `Classification.SupercuspidalContragredientAux`, imported through
  `Smooth.SmallRealizationProof` for the countability certificate of `GL_N`.
  None of them states or proves an excluded result, and no supercuspidal
  conclusion is used by this proof.
- **Proposition definitions.** The proposition definitions
  whose truth enters, directly or inside the cited published proofs, are proved
  by published theorems (`ClosedSubgroupMackeyFiltration`,
  `ClosedOrbitSectionExtension`, `ParabolicQuotientCompactClause`); the
  target `MirabolicProductRestrictionStatement` is only the conclusion. The
  further proposition definitions reached through the two elementary lemma
  modules (`MirabolicModularCharacterStatement`,
  `MirabolicRadicalHaarModulusStatement`, `LastRowCompactOrbitStatement`,
  `ZeroRowLastRowCutoffStatement`, `GeneralLinearHaarRightInvariantStatement`,
  `UnipotentHaarRightInvariantStatement`, `ProjectionAndNaturality` and the
  p-adic Fourier and conductor statements of `LocalFactor.Harmonic.Statement`)
  do not enter: the proofs of the two lemmas used are the Mathlib computations
  described above. No unproved statement,
  citation or conditional assembly is used as an input.
- **Conventions.** The supplied `T` and `T.topology` are used
  throughout, with the published explicit normalizations: the binary product's
  `δ_P^(1/2)`, and the mixed products' characters, including the case (III)
  factor `ε`, which `leviHalfModulus_eq_rightLeviCharacter` matches exactly. No
  scalar or character twist is suppressed, no rank-zero `GL` input or `P_0` is
  introduced, and input objects are arbitrary `SmoothRep.{0,uF,uV} ℂ`
  representations with output universe `max uF uV`.
