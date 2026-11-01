# Unnormalized `Φ⁻` through the plus subgroup, and the two-orbit sequence

Author: Worker 837.

This helper module serves the positive-rank `Φ⁻` sequence of BZ77
Proposition 4.13(c), the clause `RightPhiShortExact` of
`Langlands.Derivative.MirabolicProductMinusCompatibilityStatement` (host task
`6cd54f76-f453-4faa-818a-5843e1bbcaff`). It proves no clause of that
proposition and does not import the statement module. It contains three
generic pieces:

1. the character localization defining unnormalized `Φ⁻`, written for
   arbitrary representations of the plus subgroup `Q = P_(t+1) V_(t+2)` of
   `P_(t+2)`, and its natural identification with the published
   `phiMinusUnnormalized` after restriction to `Q`;
2. exactness of this localization on short exact sequences of
   `Q`-representations with smooth middle term;
3. for a closed subgroup `H` of `P_(t+2)` and an ordered enumeration of two
   `(H, Q)` double-coset orbits, a natural short exact sequence whose middle
   term is unnormalized `Φ⁻` of compact induction from `H` and whose outer
   terms are the localized published orbit pieces.

No orbit enumeration, orbit-piece identification, Haar modulus, determinant
normalization or mixed product appears here. Those are the concrete parts of
the clause and are proved elsewhere.

## Original and derived provenance

The registered original is Bernstein and Zelevinsky, *Induced
representations of reductive p-adic groups I* (1977),
`bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.

- §3.2, printed pp.450–451 (PDF pages 11–12): `Φ⁻ = r_{V,θ}`, the
  `θ`-localization by the last-column radical with the smaller mirabolic
  acting. The published `phiMinusUnnormalized` implements it without the
  §1.8 normalization; see `Derivative/MirabolicMinus.md`.
- §7.2, printed p.471 (PDF page 32): the proof of 4.13(b,c) restricts the
  induced representation to `P_(n-1) V_n`, applies the geometric lemma
  (Theorem 5.2) to the two orbits, and localizes. This module is the generic
  part of that step.

Everything here is derived. That `Φ⁻` only depends on the restriction to
`Q` holds because the radical `V_(t+2)` lies in `Q` and the successor copy of
`P_(t+1)` acts. Theorem 5.2 enters only through the published
`Geometric.closedSubgroupMackeyFiltration`, the closed-subgroup Mackey
filtration with trivial localization data, and its two-step corollary
`RepFunctorFiltration.exists_exact_of_two`. Exactness of localization enters
through the published `Jacquet.Localization.characterLocalizationExactness`.

## Conventions

`mirabolic (t + 1) F` is the source's `P_(t+2)`. `plusSubgroup t F` is
`Q = P_(t+1) V_(t+2)`, with `plusProjection : Q →* P_(t+1)`,
`plusSuccessor : P_(t+1) →* Q` and `plusRadical : V_(t+2) →* Q`
(`Group/GL/MirabolicProjection`). `thetaPlus ψ t : Q →* ℂˣ` is the published
character `q ↦ ψ(q_(t,t+1))` (`Derivative/MirabolicPlus`), equal to `θ_ψ` on
the radical and trivial on the successor copy.

## The kernel and its character

For a commutative ring `R`:

- `plusKernel t R := (plusProjection).ker`, a subgroup of `Q`;
- `plusSuccessorRange t R := (plusSuccessor).range`, and
  `plusSuccessorToRange t R := (plusSuccessor).rangeRestrict`;
- `plusSuccessorRange_le_normalizer`: the range normalizes the kernel,
  because a kernel is normal;
- `plusKernel_val_mem` and `plusKernelEquiv : plusKernel t R ≃* radical (t+1) R`,
  sending `u` to its underlying matrix, with inverse `u ↦ plusRadical u`;
  `plusKernelEquiv_val` is `rfl`.

With a topology on `R`, `continuous_plusKernelEquiv`,
`continuous_plusKernelEquiv_symm` and `continuous_plusSuccessorToRange` hold.
For `ψ : UnitaryAdditiveCharacter R`:

- `plusKernelTheta ψ t := (thetaPlus ψ t).comp (plusKernel t R).subtype`;
- `plusKernelTheta_apply`: `plusKernelTheta ψ t u = theta ψ t (plusKernelEquiv u)`,
  by `rfl`;
- `plusKernelTheta_isInvariant`: the character is invariant under
  conjugation by the successor range. It is the restriction of a
  homomorphism of `Q` to the commutative group `ℂˣ`, so
  `thetaPlus(m u m⁻¹) = thetaPlus(u)`.

## The localization on `Q`

```lean
def plusPhiLocalization (ψ : UnitaryAdditiveCharacter R) (t : ℕ) :
    Rep.{uV} ℂ (plusSubgroup t R) ⥤ Rep.{uV} ℂ (mirabolic t R)
```

is the published `Jacquet.Localization.functor` at
`(plusKernel t R, plusKernelTheta ψ t, plusSuccessorRange t R)` followed by
Mathlib's restriction along `plusSuccessorToRange t R`. It has no
normalization twist. Its laws are:

- `plusPhiLocalization_obj_carrier`: the carrier is the actual quotient
  `Jacquet.Localization.Coinvariants A.ρ (plusKernel t R) (plusKernelTheta ψ t)`;
- `plusPhiLocalization_action`: `g • [v] = [A.ρ (plusSuccessor g) v]`;
- `plusPhiLocalization_map_mk`: maps send `[v]` to `[f v]`.

All three are `rfl`.

## Comparison with `phiMinusUnnormalized`

For `T : F.TopologicalData`, `ψ` and `t`, and a smooth representation `A` of
`P_(t+2)`, `plusPhiLocalizationEquiv T ψ t A` is a `Representation.Equiv`
from `plusPhiLocalization ψ t` of the restriction of `A` to `Q` to
`phiMinusUnnormalized T ψ t` of `A`. Its linear part is the published
`Jacquet.Localization.transportEquiv` along `plusKernelEquiv` and the
identity of `A`. The character condition is `rfl` by
`plusKernelTheta_apply`. It sends classes to classes
(`plusPhiLocalizationEquiv_mk`, `rfl`). Both actions send `[v]` to
`[A(successor g) v]`, so equivariance is checked on representatives.

`plusPhiLocalizationIso T ψ t` is the resulting natural isomorphism

```text
SmoothRep.toRep ⋙ Rep.resFunctor Q.subtype ⋙ plusPhiLocalization ψ t
  ≅ phiMinusUnnormalized T ψ t ⋙ SmoothRep.toRep
```

of functors from smooth representations of `P_(t+2)` to `Rep ℂ P_(t+1)`.
Naturality is checked on representatives.

## Exactness

`plusPhiLocalization_exact T ψ t i q hi hq hex hB`: let `i : A ⟶ B` and
`q : B ⟶ C` be morphisms of `Rep ℂ Q`, with `i` injective, `q` surjective,
`range i = ker q` and `B` smooth for the supplied topology. Then the maps of
`plusPhiLocalization ψ t` have the same three properties. The proof applies
the published `characterLocalizationExactness` on the topological group `Q`.
Its two premises are proved here:

- the kernel is a union of compact subgroups: a compact subset is carried by
  `plusKernelEquiv` into the radical, where the published
  `radical_isLimitOfCompactSubgroups` gives a compact subgroup, and its image
  under the continuous inverse contains the subset;
- the character is locally constant: it is `θ_ψ ∘ plusKernelEquiv`, and
  `θ_ψ` has open kernel (`mirabolicTheta_isOpen_ker`). A private copy of the
  elementary fact "open kernel implies locally constant" is included.

## The two-orbit sequence

Let `H` be a closed subgroup of `P_(t+2)` and
`s : Geometric.OrderedDoubleCosets H Q 2` an ordered enumeration of its two
`(H, Q)` orbits. The open-initial-union condition is part of `s`.

`exists_exact_plusPhiLocalization T ψ t H hH s` gives natural transformations

```text
i : orbitPiece H Q (s.representative 0) ⋙ plusPhiLocalization ψ t
      ⟶ restrictedCompactInduction H Q ⋙ plusPhiLocalization ψ t
q : restrictedCompactInduction H Q ⋙ plusPhiLocalization ψ t
      ⟶ orbitPiece H Q (s.representative 1) ⋙ plusPhiLocalization ψ t
```

of functors on smooth representations of `H`. At every object, `i` is
injective, `range i = ker q` and `q` is surjective. The proof constructs the
l-group instances on `P_(t+2)`: nonarchimedean from `GL_(t+2)`, locally
compact from the published `Mirabolic.locallyCompactSpace`, Hausdorff and
σ-compact as a closed subset. It uses the published closedness of `Q`, and
the published Mackey filtration gives the two graded-piece isomorphisms.
`exists_exact_of_two` gives a natural short exact sequence of
`Q`-representations, and the sequence is whiskered by
`plusPhiLocalization`. Exactness follows from `plusPhiLocalization_exact`.
The middle term is smooth because compact induction is smooth and restriction
to `Q` preserves smoothness.

`exists_exact_phiMinusUnnormalized_compactInduction T ψ t H hH s` replaces the
middle term by

```text
(SmoothRep.toRep ⋙ Induction.compactInductionFunctor H) ⋙
  phiMinusUnnormalized T ψ t ⋙ SmoothRep.toRep,
```

through `plusPhiLocalizationIso` whiskered on the left by compact induction.
The orbit pieces are unchanged. Universes `uF` and `uV` are independent; the
orbit pieces and the induced representations have carriers in `max uF uV`.

`exact_comp_isos` is the generic step used here. In any functor category
into `Rep R G`, pointwise short exactness of `(i, q)` is preserved by
composing with natural isomorphisms `eA`, `eB`, `eD` at the three positions:
`(eA.hom ≫ i ≫ eB.hom, eB.inv ≫ q ≫ eD.hom)`. The proof is elementwise.

Both Mackey theorems use `set_option maxHeartbeats 800000`. They are slow to
elaborate, but no unfolding is needed.

## Mathematical dependency and restriction audit

The direct imports are the published
`Langlands.Representation.Derivative.MirabolicPlus`,
`Langlands.Representation.Derivative.MirabolicMinusExactnessProof`,
`Langlands.Representation.Derivative.MirabolicProductRestrictionMackey` and
`Langlands.Representation.Jacquet.LocalizationTransport`. Every imported
module is independently accepted and published. No Library module is
modified. Proposition definitions in the closure supply types; none is used
as a proof of its conclusion.

| Condition | Actual dependency and scope |
| --- | --- |
| Minus functors | `phiMinusUnnormalized`, `phiMinusQuotient` and `continuousPullbackFunctor` (published `MirabolicMinus`) are used unchanged. `MirabolicMinusExactnessProof` supplies only `radical_isLimitOfCompactSubgroups`; no normalized minus functor is used. |
| Plus subgroup data | `plusSubgroup`, `plusProjection`, `plusSuccessor`, `plusRadical` and their laws are group constructions (published `MirabolicProjection`). From `MirabolicPlus` only the character `thetaPlus` is used; on the radical it is `θ_ψ` by definition. No `Ψ⁺` or `Φ⁺` functor, plus-functor theorem, adjunction or exactness of a plus functor is used. |
| Localization exactness | The published `characterLocalizationExactness` (`Jacquet.LocalizationExactnessProof`) proves exactness of character localization from compact detection of relations and smooth averaging. It uses no finiteness or classification input. |
| Mackey filtration | `closedSubgroupMackeyFiltration` (published `Geometric.ClosedSubgroupMackeyProof`) is the closed-subgroup geometric lemma with trivial localization data. Its inputs are the published orbit-section extension and coset-orbit homeomorphism. The orbit enumeration `s` is a hypothesis of this module and is not proved here. |
| Restriction-sequence module | `MirabolicProductRestrictionMackey` supplies only the generic `RepFunctorFiltration.exists_exact_of_two`. Its theorem `exists_exact_restrictedCompactInduction` and its imports `MirabolicProductRestrictionOrbits` and `MinusVanishing` are not used. No BZ77 4.13(a) conclusion is used, and the separate restriction-sequence owner is not duplicated. |
| Countability and its closure | `Group.GL.CountabilityProof` (through the Mackey module) supplies σ-compactness of `GL_n`. Its import `Smooth.SmallRealizationProof` brings definitions of supercuspidality, contragredients and admissibility (`Classification.Supercuspidal*`, `Smooth.Contragredient.*`, `Smooth.Admissibility.*`). They are definitions and lower laws; no supercuspidal or finiteness conclusion is used. |
| Rankin–Selberg and Whittaker modules in the closure | `RankinSelberg.Measures`, `QuotientIntegrals`, the unimodularity and last-row cutoff modules and `Whittaker.Algebraic` and `Whittaker.GeneralLinear` come with the generic induction and orbit infrastructure. They provide measure, compact-orbit and character constructions only. |
| Structural induction statement | `Induction.StructuralStatement` supplies proposition definitions only, including `OpenSubgroupAdjunctionClause`; none is used as a proof. |
| BZ77 4.13(d) and general Leibniz | No submodule-detection conclusion, general Leibniz proof or derivative-filtration theorem is used. `Filtration.Definitions` and `Filtration.QuotientFirstIso` supply filtration definitions and the first isomorphism theorem. |
| Segment derivative and Jacquet formulas | No segment derivative formula, Ze80 §3.5 or §9.6, `SegmentFullJacquetFormula`, `SegmentHeadJacquetFormula`, `SegmentSocleJacquetFormula` or `SegmentSpecialJacquetExponentNormFormula` supplies a direct or transitive input. |
| Individual segment existence | No individual special-head/reverse-socle or segment-socle/reverse-head existence conclusion, proof successor or downstream consequence is used. |
| Linked and unlinked socle consumers | `UnlinkedSegmentSocleProductIrreducible`, `LinkedSegmentSocleReverseProductStructure`, `LinkedSegmentSoclePairReducible`, `JuxtaposedSegmentSocleReverseProductStructure` and `LinkedSegmentSocleReverseProductQuotientHom` are absent from the dependencies. |
| Segment product and commutation consumers | No `SegmentSocleProductIrreducibility`, `AdjacentUnlinkedSegmentSocleSwap`, `TwoSegmentSocleCommutation`, `LinkedSegmentSocleGluing`, Ze80 4.2 or 9.7 criterion, or their successors or consequences is used. |
| Special-head criterion and uniqueness | `SegmentHeadProductIrreducibility` and `GenericSegmentProductUniqueness`, their parent tasks, successors and downstream consequences supply no input. |
| Ordered existence and multisegment exhaustion | No `OrderedMultisegmentSocleExistence`, `MultisegmentSocleExhaustion`, ordered strong-head existence, special-head multisegment exhaustion, quotient coverage or ordered-conversion conclusion is used. |
| Analytic, tempered and square-integrable classification | No analytic segment classification, `SegmentSpecialEssentialSquareIntegrability`, tempered uniqueness, `SquareIntegrableLanglandsClassification`, square-integrable or regular exhaustion, or Ze80 9.3 conclusion is used, including their successors and consequences. |
| Two-supercuspidal consumers | Neither `TwoSupercuspidalNonadjacentProductIrreducible` nor `TwoSupercuspidalProductStructure`, their full-product assembly, successors or consequences is imported or used. |
| Supercuspidal and single-block finiteness | No `SupercuspidalCoinvariantFinitenessStatement`, all-character single-block conclusion or downstream consequence supplies an input. No arbitrary-character finiteness theorem is used. |
| Other Whittaker finiteness exclusions | `IrreducibleCoinvariantFinitenessStatement` and `LeviCuspidalCoinvariantFinitenessStatement`, their parent and proof tasks and their consequences are absent, as is the prohibited mirabolic finite-length route. |
| Host clauses and pending results | No host clause, mixed product, orbit-coverage proof, pending candidate, draft or consumer conclusion is imported or used. |
| Parameters | `T`, `ψ`, `t`, the closed subgroup `H`, the orbit enumeration and all smooth carriers, including zero modules, are arbitrary. |

These rows cover every named task in the host's inherited exclusion union,
its mathematical conclusions, proof successors and downstream consequences.
A search over the source of the closure below and of this module found no
excluded declaration name and no task identifier in Lean code. The only match
of the word `Adjunction` is `OpenSubgroupAdjunctionClause`, noted above. The
search also found no `sorry`, `admit`, `native_decide` or new axiom.
`exists_exact_phiMinusUnnormalized_compactInduction` depends only on
`propext`, `Classical.choice` and `Quot.sound`.

## Complete project import closure

There are exactly 137 transitive project imports, excluding this module, at
Library base `4bec44eec4c7f23def3d25d5c43f4f2a034af469`. The list is computed
from the actual import lines. Every entry is published, and its Lean/Markdown
pair in the workspace is byte-identical to that commit. Mathlib dependencies
come from the pinned Lean environment.

```text
Langlands.Analysis.Local.QuotientMeasure
Langlands.Analysis.Local.QuotientTopology
Langlands.Group.GL.Basic
Langlands.Group.GL.Blocks
Langlands.Group.GL.CompactOpen
Langlands.Group.GL.CountabilityProof
Langlands.Group.GL.CountabilityStatement
Langlands.Group.GL.Maps
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
Langlands.Group.GL.PadicOppositeBlocks
Langlands.Group.GL.PadicUpperUnipotent
Langlands.Group.GL.RankMaps
Langlands.Group.GL.UpperUnipotent
Langlands.Group.GL.UpperUnipotentCompactContainmentProof
Langlands.Group.GL.UpperUnipotentCompactContainmentStatement
Langlands.HarmonicAnalysis.Basic
Langlands.HarmonicAnalysis.Conductor
Langlands.HarmonicAnalysis.PadicAdditiveConductorProof
Langlands.HarmonicAnalysis.PadicHaarScalingStatement
Langlands.HarmonicAnalysis.PadicLatticeTopology
Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof
Langlands.LocalFactor.Harmonic.Statement
Langlands.LocalField.Canonical
Langlands.LocalField.Definitions
Langlands.LocalField.Normalization.Definitions
Langlands.LocalField.Normalization.Proof
Langlands.LocalField.Normalization.Statement
Langlands.LocalField.Topology
Langlands.Representation.Category.Basic
Langlands.Representation.Category.Twist
Langlands.Representation.Classification.Supercuspidal
Langlands.Representation.Classification.SupercuspidalContragredientAux
Langlands.Representation.Classification.SupercuspidalContragredientStatement
Langlands.Representation.Compact.Definitions
Langlands.Representation.Compact.FiniteMean
Langlands.Representation.Compact.OrbitMeanTranslation
Langlands.Representation.Compact.ProjectionProof
Langlands.Representation.Compact.ProjectionStatement
Langlands.Representation.Conductor.Congruence
Langlands.Representation.Derivative.MinusVanishing
Langlands.Representation.Derivative.MirabolicCharacter
Langlands.Representation.Derivative.MirabolicLatticeBox
Langlands.Representation.Derivative.MirabolicMinus
Langlands.Representation.Derivative.MirabolicMinusExactnessProof
Langlands.Representation.Derivative.MirabolicMinusExactnessStatement
Langlands.Representation.Derivative.MirabolicPlus
Langlands.Representation.Derivative.MirabolicProductRestrictionMackey
Langlands.Representation.Derivative.MirabolicProductRestrictionOrbits
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
Langlands.Representation.Induction.CompactLocalSection
Langlands.Representation.Induction.CompactQuotientCutoff
Langlands.Representation.Induction.CompactQuotientProof
Langlands.Representation.Induction.Definitions
Langlands.Representation.Induction.StructuralStatement
Langlands.Representation.Jacquet.CharacterAveraging
Langlands.Representation.Jacquet.Coinvariants
Langlands.Representation.Jacquet.ExactProof
Langlands.Representation.Jacquet.ExactStatement
Langlands.Representation.Jacquet.Localization
Langlands.Representation.Jacquet.LocalizationExactnessProof
Langlands.Representation.Jacquet.LocalizationExactnessStatement
Langlands.Representation.Jacquet.LocalizationTransport
Langlands.Representation.Jacquet.SmoothTwist
Langlands.Representation.MatrixCoefficient.Definitions
Langlands.Representation.MatrixCoefficient.LawsProof
Langlands.Representation.MatrixCoefficient.LawsStatement
Langlands.Representation.OrbitSpan
Langlands.Representation.RankinSelberg.LastRowCompactOrbitProof
Langlands.Representation.RankinSelberg.LastRowCompactOrbitStatement
Langlands.Representation.RankinSelberg.Measures
Langlands.Representation.RankinSelberg.QuotientIntegrals
Langlands.Representation.RankinSelberg.UnimodularityStatement
Langlands.Representation.RankinSelberg.UnipotentUnimodularity
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
Langlands.Representation.Smooth.SmoothPart.Definitions
Langlands.Representation.Smooth.SmoothPart.FixedVectorsDefinitions
Langlands.Representation.Smooth.Transfer.PullbackProof
Langlands.Representation.Smooth.Transfer.PullbackStatement
Langlands.Representation.Smooth.Transfer.SubquotientProof
Langlands.Representation.Smooth.Transfer.SubquotientStatement
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
Langlands.Topology.CompactNormCharacter
Langlands.Topology.CompactOpen.NeighborhoodBasis
Langlands.Topology.CompactOpen.NeighborhoodBasisStatement
Langlands.Topology.Nonarchimedean.Subgroup
```
