# Proof of Zelevinsky 5.3: homogeneity of left mixed products

Authors: Worker 1129 and Worker 749. Module
`Langlands.Representation.Derivative.LeftMixedProductHomogeneityProof`,
namespace `Langlands.Derivative`. Main theorem:

```lean
theorem leftMixedProductHomogeneity
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    LeftMixedProductHomogeneity.{uF, uV} F T
```

It proves the published proposition
`Langlands.Derivative.LeftMixedProductHomogeneity`
(`Langlands.Representation.Derivative.LeftMixedProductHomogeneityStatement`)
for arbitrary `p`, `F`, `T` and independent universes `uF`, `uV`, with no
further hypothesis. The module contains no other declaration; in particular
there is no conditional variant taking BZ77 4.14(a) as a premise.

## Statement

For every unitary additive character `ψ`, all `k r : ℕ`, every smooth
representation `ρ` of `GL_k` and every smooth representation `τ` of the
mirabolic group `P_(r+1)` (Library `mirabolic r`; carriers in a universe
`uV`), if `τ` is homogeneous, then the left mixed product `ρ × τ`
(`(T.leftMixedProductFunctor k r).obj (ρ, τ)`, a representation of
`P_(k+r+1)` with carrier in `max uF uV`) is homogeneous. Here
`IsHomogeneous T ψ A` means that every nonzero subrepresentation of `A` has
the level of `A` (`Langlands.Derivative.IsHomogeneous` and
`Langlands.Derivative.level`, module `Derivative.Homogeneity`), with the
same `ψ` on both sides.

## Sources

Zelevinsky, *Induced representations of reductive p-adic groups II* (1980),
literature ID `zelevinsky-1980-induced-ii`, SHA256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac` (printed
page = PDF page + 163): §5.3, printed pp.187–188 (PDF pp.24–25), and §5.1,
printed p.187 (PDF p.24), Proposition, (1) ⇔ (3).

Bernstein–Zelevinsky, *Induced representations of reductive p-adic groups I*
(1977), literature ID `bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092` (printed
page = PDF page + 439): §3.2, printed pp.450–451 (PDF pp.11–12; the functors
and adjunctions), §4.12 case (II), printed pp.456–458 (PDF pp.17–19; the
product), and Corollary 4.14(a), printed p.458 (PDF p.19):
`(ρ × τ)^(i) = ρ × τ^(i)`.

Ze80 5.3 argues: let `λ(τ) = l` and `θ = τ^(l)`. By 4.14(a),
`λ(ρ × τ) = l` (for `ρ ≠ 0`). By 5.1, `τ ↪ (Φ̂⁺)^(l-1) Ψ⁺(θ)`, so
`ρ × τ ↪ ρ × (Φ̂⁺)^(l-1) Ψ⁺(θ) ↪ (Φ̂⁺)^(l-1) Ψ⁺(ρ × θ)`, and by 5.1, (3) ⇒
(1), `ρ × τ` is homogeneous. The proof below follows this outline, with two
changes described after the proof: it never compares `ρ × Ψ⁺(θ)` with
`Ψ⁺(ρ × θ)`, and it needs no nonvanishing hypothesis on `ρ`.

## Proof

Fix `ψ, k, r, ρ, τ` with `τ` homogeneous, and a subrepresentation `U ≠ ⊥` of
`ρ × τ`, with carrier representation `W = SmoothRep.subrepresentation _ U`.
We show `λ(W) = λ(ρ × τ)`.

1. Upper bound `λ(W) ≤ λ(ρ × τ)`: the inclusion `W ↪ ρ × τ`
   (`SmoothRep.subtype`, injective by `SmoothRep.subtype_injective`) and
   `LevelCalculus.level_le_of_injective`, whose exactness hypothesis is
   discharged by the published minus exactness proof
   `Langlands.Derivative.Mirabolic.minusExactness.{uF, max uF uV} F T`. (The
   product has carriers in `max uF uV`, hence that universe instance.)
2. `λ(ρ × τ) ≤ λ(τ)`: `RestrictedProductLevel.level_leftMixed_le T ψ hLD ρ τ`,
   where `hLD` is the term `leftMixedProductDerivative.{uF, uV} F T`, the
   published BZ77 4.14(a) theorem (module
   `Langlands.Representation.Derivative.LeftMixedProductDerivativeProof`),
   applied inside the proof. That lemma shows that a nonzero derivative of
   order `i` of `ρ × τ` gives one of `τ`: for `i ≤ r + 1` through the
   4.14(a) isomorphism `(ρ × τ)^(i) ≅ ρ × τ^(i)` and the vanishing of a
   binary product with a zero factor (`ProductVanishing.subsingleton_binary`),
   and for `i > r + 1` by the 4.14(a) vanishing clause.
3. If `λ(τ) = 0`, then steps 1 and 2 give `λ(W) = 0 = λ(ρ × τ)` (`omega`).
4. Otherwise `l = λ(τ)` satisfies `0 < l ≤ r + 1` (`level_le`). Since `τ` is
   homogeneous of level `l`, the unit
   `η_τ = mirabolicDerivativeOfOrderUnit T ψ r l hl τ : τ ⟶ Y_l(τ^(l))` is
   injective (`mirabolicDerivativeOfOrderUnit_injective`, Ze80 5.1
   (1) ⇒ (3), module `Derivative.MirabolicDerivativeUnitInjective`, Worker
   749). Here `Y_l(θ) = (Φ̂⁺)^(l-1) Ψ⁺(θ)` is
   `mirabolicDerivativeOfOrderRightAdjoint`, built from the smooth induction
   `Φ̂⁺` of BZ77 §3.2, not the compact `Φ⁺`.
5. Lower bound: `Mirabolic.hasNonzeroDerivative_leftMixed_subrepresentation`
   (module `Derivative.LeftMixedProductPhiHatIterate`, Worker 1129) applied
   to `η_τ`, its injectivity and `U ≠ ⊥` gives `HasNonzeroDerivative T ψ W l`,
   so `l ≤ λ(W)` (`le_level_of_hasNonzeroDerivative`). That theorem embeds
   `ρ × τ ↪ ρ' × Y_l(θ)` (with `ρ'` the universe lift of `ρ`), and peels the
   `Φ̂⁺` factors off one at a time with the published embedding
   `ρ × Φ̂⁺(σ) ↪ Φ̂⁺(ρ × σ)` (`leftPhiHatEmbedding`, module
   `Derivative.MirabolicSmoothPhiPlusProduct`) and the adjunction
   `Φ⁻ ⊣ Φ̂⁺`, until the target is `ρ' × Ψ⁺(θ)`, on which the radical acts
   trivially; there the nonzero map factors through `Ψ⁻`.
6. Steps 1, 2 and 5 give `l ≤ λ(W) ≤ λ(ρ × τ) ≤ l` (`omega`).

Differences from the source. Step 5 replaces the comparison of
`ρ × Ψ⁺(θ)` with `Ψ⁺(ρ × θ)` and the second use of 5.1 (see the Markdown of
`LeftMixedProductPhiHatIterate`). The source assumes `ρ ≠ 0` and uses the
equality `λ(ρ × τ) = λ(τ)`; the proof only needs the inequality of step 2,
which holds for every `ρ`, so the nonvanishing of `ρ × θ` is not needed.

Boundary cases. The argument has no case split on `ρ`, `τ`, `k` or `r`:
every lemma used holds for all `k` (including `k = 0`, an arbitrary `GL_0`
representation), all `r` (including `r = 0`) and all smooth `ρ`, `τ`. If
`ρ` or `τ` is zero, then `ρ × τ` has no nonzero subrepresentation and the
statement holds trivially; the proof above covers this case without
treating it separately. Level `0` is step 3.

The `lean_check` inspection of `leftMixedProductHomogeneity` (Lake build of
this module over Library `b4b4160d118213b51ef28eb814f1828ac3902ada`, no
errors or warnings) reports the universe parameters `uF, uV` and only the
axioms `propext`, `Classical.choice` and `Quot.sound`.

## Published inputs

All of these are accepted and published; they are imported by Lean name.

| Lean input | Role | Artifact, task |
| --- | --- | --- |
| `Mirabolic.minusExactness` | step 1, exactness | `d307cd07-7e0f-4e38-a3d5-94b78bb3a7d6` (`lean.proof@1` of `MinusExactnessStatement`), task `b65bc667` |
| `leftMixedProductDerivative` | step 2, BZ77 4.14(a) | `e99bbe1b-06fe-42ad-b8ec-d1c4e02c9929` (`lean.proof@1` of `LeftMixedProductDerivative`, statement artifact `845a8c59`), task `7e19f753`, arranged by statement task `f9454f68` revision 2 (Workers 1190, 1018) |
| `RestrictedProductLevel.level_leftMixed_le`, `LevelCalculus.level_le_of_injective` | steps 1, 2 | `6ded142e-bf04-4d18-8956-a5850e80410b` (conditional helpers: exactness and 4.14(a) are explicit hypotheses, discharged here) |
| `mirabolicDerivativeOfOrderUnit_injective` | step 4, Ze80 5.1 (1) ⇒ (3) | `bab82164-3d53-442c-9d38-68716515bd3a` (Worker 749, this task) |
| `Mirabolic.hasNonzeroDerivative_leftMixed_subrepresentation` | step 5 | `ac76e357-e093-4ff7-85ef-a796f74cdb16` (Worker 1129, this task) |
| `level_le`, `le_level_of_hasNonzeroDerivative`, `SmoothRep.subtype_injective` | steps 3–5 | `Derivative.Homogeneity`, `Category.Subquotients` (Library definitions and elementary lemmas) |

The 4.14(a) proof uses BZ77 4.13(b) only through the published component
proofs of proof task `6cd54f76-f453-4faa-818a-5843e1bbcaff` of statement task
`763a8cf3-356a-43dd-a617-6a2839fdb0cb`:
`MirabolicProductMinus.leftPsiCompatibility` (artifact `8a6a0658`),
`MirabolicProductMinus.leftPhiCompatibility` (artifact `e32e2414`) and
`MirabolicProductMinus.leftPhiBoundary` (artifact `c8340e2a`), each with
`statement_declaration` the corresponding clause of
`MirabolicProductMinusCompatibilityStatement`. Its `GL_0` case is the
published `LeftMixedProductZeroRank` of the same task `7e19f753`.

The lower inputs of `ac76e357` and `bab82164` are the published `Φ̂⁺`
constructions of this task: `Derivative.MirabolicSmoothPhiPlus`,
`MirabolicSmoothPhiPlusAdjunction`, `MirabolicSmoothPhiPlusIterate` (Worker
749), `Mirabolic.LeftMixedProductSuccessor` (`b30d26c3`) and
`Derivative.MirabolicSmoothPhiPlusProduct` (`ea098c88`) (Worker 1129), and
the published derivative detection proof
`Langlands.Derivative.mirabolicDerivativeDetection`
(`3ace613e-7e47-46fc-aea5-dcd84efc51ec`, task `ed056880`), which the
objective permits.

## Import inventory

Direct imports:

- `Langlands.Representation.Derivative.LeftMixedProductHomogeneityStatement`:
  the target proposition, unchanged.
- `Langlands.Representation.Derivative.LeftMixedProductPhiHatIterate`:
  the lower bound of step 5.
- `Langlands.Representation.Derivative.MirabolicDerivativeUnitInjective`:
  injectivity of the unit, step 4.
- `Langlands.Representation.Derivative.RestrictedProductLevel`:
  `level_leftMixed_le`, step 2.
- `Langlands.Representation.Derivative.MirabolicMinusExactnessProof`: the
  published proof `Mirabolic.minusExactness`, step 1.
- `Langlands.Representation.Derivative.LeftMixedProductDerivativeProof`: the
  published 4.14(a) proof `leftMixedProductDerivative`, step 2.

No existing Library file is changed. The transitive project import closure
at Library commit `b4b4160d118213b51ef28eb814f1828ac3902ada` has 312
modules besides this one; each has a nonempty Markdown file and is
byte-identical to the Library. 135 of them are reached only through
`LeftMixedProductDerivativeProof`: that module and the 134 modules of its
own audited 259-module closure (listed in `LeftMixedProductDerivativeProof.md`,
and equal to its current closure) that the other direct imports do not
reach. The remaining 177 are reached through the other five direct
imports; 128 of them form the audited closure of
`LeftMixedProductPhiHatIterate`.

Groups of modules in the closure:

- Foundations (128 modules audited in `LeftMixedProductPhiHatIterate.md`):
  groups, Haar moduli and local fields; smooth representations, induction,
  twists and Jacquet coinvariants; the published `Ψ⁻`, `Φ⁻`, `Ψ⁺`, `Φ⁺`,
  `Φ̂⁺`, the `Φ⁻ ⊣ Φ̂⁺` adjunctions and the product embedding; the
  derivative, level and homogeneity definitions; the published detection
  proof with its lattice-box and Rankin–Selberg compact-orbit lemmas;
  Whittaker characters and the Iwasawa decomposition.
- Proofs of published exactness: `Derivative.MirabolicMinusExactnessProof`,
  `Jacquet.ExactStatement`, `Jacquet.ExactProof`,
  `Jacquet.LocalizationExactnessStatement`,
  `Jacquet.LocalizationExactnessProof`,
  `Group.GL.UpperUnipotentCompactContainmentStatement`,
  `Group.GL.UpperUnipotentCompactContainmentProof`,
  `RankinSelberg.Measures`, `RankinSelberg.UnimodularityStatement`,
  `RankinSelberg.UnipotentUnimodularity`.
- Level calculus for products: `Derivative.RestrictedProductLevel`,
  `Derivative.RightMixedLevel`, `Derivative.RestrictionBridge`,
  `Derivative.ProductVanishing`, and the statement-only modules
  `Derivative.MixedProductDerivativeStatement` (4.13(d), 4.14(a)),
  `Derivative.MirabolicProductMinusCompatibilityStatement` (4.13(b,c)) and
  `Derivative.MirabolicProductRestrictionStatement` (4.13(a)).
- Generic filtration and length theory, imported by `ProductVanishing`
  through `Parabolic.ProductInductionSubrepresentation`: the
  `Filtration.*` Jordan–Hölder, length criterion, length-two matching,
  interval lift and graded refinement modules, `Tensor.Filtration`,
  `Tensor.FiniteFiltration`, `Tensor.ExternalFiltration`,
  `Tensor.ExternalSubrepresentation`, `Parabolic.InductionFactorMatching*`,
  `Parabolic.InductionSubrepresentation`,
  `Parabolic.ProductInductionSubrepresentation`.
- Induction surjectivity and compact open subgroups:
  `Induction.SurjectivityStatement`, `Induction.SurjectivityProof`,
  `Induction.CompactLocalSection`, `Compact.SurjectivityStatement`,
  `Compact.SurjectivityProof`, `Group.GL.CompactOpen`,
  `Group.GL.PadicOppositeBlocks`, `Group.GL.PadicUpperUnipotent`.
- This task's units: `Derivative.LeftMixedProductHomogeneityStatement`,
  `Derivative.LeftMixedProductPhiHatIterate`,
  `Derivative.MirabolicDerivativeUnitInjective`, and the `Φ̂⁺` modules above.
- The 4.14(a) proof and its inputs (135 modules): the entry
  `Derivative.LeftMixedProductDerivativeProof` with
  `LeftMixedProductHigher`, `LeftMixedProductVanishing`,
  `LeftMixedProductZeroRank`, `OrderRecursion`, `MixedProductRankCast`,
  `ZeroRankTensor`; the published 4.13(b) proofs
  `MirabolicProductMinusLeftPsi*`, `MirabolicProductMinusLeftPhi*`,
  `MirabolicProductMinusBoundary`, `MirabolicProductMinusPhiKernelComparison`
  and the 4.13(a) restriction machinery
  (`MirabolicProductRestriction{Factors,Mackey,Orbits,Transport}`); mirabolic
  mixed-orbit geometry (`Group.GL.MirabolicMixedOrbit*`,
  `Derivative.MirabolicMixedOrbitCharacters`); quotient measures and
  averaging (`Analysis.Local.Quotient*`, `ModularCompactAverage`,
  `SplitKernelQuotient`); compact induction automorphisms, transitivity,
  coinvariants, split quotients and stages (`Induction.Compact*`,
  `Induction.NormalCoinvariant*`, `Induction.SplitKernel*`,
  `Induction.SplitStages*`, `Induction.SplitQuotient*`,
  `Induction.CharacterTwistProof`, `Induction.BinaryPositiveCompact`);
  closed-subgroup Mackey theory (`Geometric.ClosedSubgroup*`,
  `Geometric.CosetAction`, `Geometric.OrbitRestriction`, …); contragredients
  and admissibility (`Smooth.Contragredient.*`,
  `Smooth.Admissibility.Equivalence*`, `Smooth.SmallRealization*`); and,
  through `Smooth.SmallRealizationProof`, `Classification.Supercuspidal`,
  `Classification.SupercuspidalContragredientAux` and
  `Classification.SupercuspidalContragredientStatement`.

Complete list of the 312 project modules in the closure, excluding this
module:

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
Langlands.Group.GL.UpperUnipotentCompactContainmentProof
Langlands.Group.GL.UpperUnipotentCompactContainmentStatement
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
Langlands.Representation.Category.Abelian
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
Langlands.Representation.Derivative.LeftMixedProductDerivativeProof
Langlands.Representation.Derivative.LeftMixedProductHigher
Langlands.Representation.Derivative.LeftMixedProductHomogeneityStatement
Langlands.Representation.Derivative.LeftMixedProductPhiHatIterate
Langlands.Representation.Derivative.LeftMixedProductVanishing
Langlands.Representation.Derivative.LeftMixedProductZeroRank
Langlands.Representation.Derivative.LevelCalculus
Langlands.Representation.Derivative.MinusVanishing
Langlands.Representation.Derivative.MirabolicCharacter
Langlands.Representation.Derivative.MirabolicDerivativeDetectionProof
Langlands.Representation.Derivative.MirabolicDerivativeDetectionStatement
Langlands.Representation.Derivative.MirabolicDerivativeUnitInjective
Langlands.Representation.Derivative.MirabolicDerivativeVanishing
Langlands.Representation.Derivative.MirabolicDeterminant
Langlands.Representation.Derivative.MirabolicLatticeBox
Langlands.Representation.Derivative.MirabolicMinus
Langlands.Representation.Derivative.MirabolicMinusExactnessProof
Langlands.Representation.Derivative.MirabolicMinusExactnessStatement
Langlands.Representation.Derivative.MirabolicMinusNormalization
Langlands.Representation.Derivative.MirabolicMixedOrbitCharacters
Langlands.Representation.Derivative.MirabolicPlus
Langlands.Representation.Derivative.MirabolicPlusNormalization
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
Langlands.Representation.Derivative.MirabolicProductRestrictionStatement
Langlands.Representation.Derivative.MirabolicProductRestrictionTransport
Langlands.Representation.Derivative.MirabolicSmoothPhiPlus
Langlands.Representation.Derivative.MirabolicSmoothPhiPlusAdjunction
Langlands.Representation.Derivative.MirabolicSmoothPhiPlusIterate
Langlands.Representation.Derivative.MirabolicSmoothPhiPlusProduct
Langlands.Representation.Derivative.MixedProductDerivativeStatement
Langlands.Representation.Derivative.MixedProductRankCast
Langlands.Representation.Derivative.OrderRecursion
Langlands.Representation.Derivative.ProductVanishing
Langlands.Representation.Derivative.RestrictedProductLevel
Langlands.Representation.Derivative.RestrictionBridge
Langlands.Representation.Derivative.RightMixedLevel
Langlands.Representation.Derivative.ShortExactFunctorLaws
Langlands.Representation.Derivative.ZeroRankTensor
Langlands.Representation.Dual.Definitions
Langlands.Representation.Filtration.Definitions
Langlands.Representation.Filtration.GradedRefinementProof
Langlands.Representation.Filtration.GradedRefinementStatement
Langlands.Representation.Filtration.IntervalLiftProof
Langlands.Representation.Filtration.IntervalLiftStatement
Langlands.Representation.Filtration.IsoTransport
Langlands.Representation.Filtration.JordanHolderStatement
Langlands.Representation.Filtration.JordanHolderTransportProof
Langlands.Representation.Filtration.LengthCriterionProof
Langlands.Representation.Filtration.LengthCriterionStatement
Langlands.Representation.Filtration.LengthTwoMatching
Langlands.Representation.Filtration.LengthTwoMatchingStatement
Langlands.Representation.Filtration.ObjectDefinitions
Langlands.Representation.Filtration.ObjectTransport
Langlands.Representation.Filtration.QuotientFirstIso
Langlands.Representation.Filtration.RepresentationLength
Langlands.Representation.Geometric.ClosedSubgroupAssembly
Langlands.Representation.Geometric.ClosedSubgroupDefinitions
Langlands.Representation.Geometric.ClosedSubgroupMackeyProof
Langlands.Representation.Geometric.ClosedSubgroupStatement
Langlands.Representation.Geometric.CompactOrbitRestriction
Langlands.Representation.Geometric.CompactSmoothComparison
Langlands.Representation.Geometric.CosetAction
Langlands.Representation.Geometric.CosetOrbitHomeomorph
Langlands.Representation.Geometric.OrbitRestriction
Langlands.Representation.Geometric.OrbitSectionExtensionProof
Langlands.Representation.Geometric.OrbitSectionExtensionStatement
Langlands.Representation.Geometric.SmoothSupportFiltration
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
Langlands.Representation.Induction.Equivalences
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
Langlands.Representation.Mirabolic.LeftMixedProductSuccessor
Langlands.Representation.Mirabolic.MixedProducts
Langlands.Representation.OrbitSpan
Langlands.Representation.Parabolic.GeometricPrerequisitesStatement
Langlands.Representation.Parabolic.InductionFactorMatchingProof
Langlands.Representation.Parabolic.InductionFactorMatchingStatement
Langlands.Representation.Parabolic.InductionSubrepresentation
Langlands.Representation.Parabolic.ProductInductionSubrepresentation
Langlands.Representation.Parabolic.QuotientCompactProof
Langlands.Representation.RankinSelberg.GeneralLinearUnimodularity
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
Langlands.Representation.Smooth.SmoothPart.BasicProof
Langlands.Representation.Smooth.SmoothPart.BasicStatement
Langlands.Representation.Smooth.SmoothPart.Definitions
Langlands.Representation.Smooth.SmoothPart.FixedVectorsDefinitions
Langlands.Representation.Smooth.Transfer.PullbackProof
Langlands.Representation.Smooth.Transfer.PullbackStatement
Langlands.Representation.Smooth.Transfer.SubquotientProof
Langlands.Representation.Smooth.Transfer.SubquotientStatement
Langlands.Representation.Tensor.ExternalFiltration
Langlands.Representation.Tensor.ExternalSubrepresentation
Langlands.Representation.Tensor.Filtration
Langlands.Representation.Tensor.Finite
Langlands.Representation.Tensor.FiniteEquivalences
Langlands.Representation.Tensor.FiniteFiltration
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

## Exclusion audit

Against the exclusions of task `6bb62ea4-c7e1-4325-9eb6-b8bbee1f65c4`
(objective and `context.md`), condition by condition. The 135 modules
reached only through the 4.14(a) proof were audited, against the same two
inherited exclusion sets, in the reviewed and published Markdown
`LeftMixedProductDerivativeProof.md`; this audit relies on that audit for
their bodies and adds the checks below.

- Inherited exclusion set of `b711af72` (ordered-socle existence
  `23189526` and socle exhaustion `f3a69bc8`, analytic segment
  classification `aca8805b`, segment-socle product irreducibility
  `23e98d90` and its criterion `2ae5cbe5`, `AdjacentUnlinkedSegmentSocleSwap`,
  `TwoSegmentSocleCommutation`, special-head criterion `8364e73f`,
  special-head exhaustion `3bfb61fa`, ordered special-head existence
  `ebea9a8a`, quotient coverage `20e4e1c6`, tempered uniqueness `52e97845`,
  `SquareIntegrableLanglandsClassification` / `1cb45da2`, square-integrable
  exhaustion `cd8ab97c`, regular exhaustion `bf433f0a`,
  `GenericSegmentProductUniqueness` / `30341ae4`, ordered conversion
  `8252833d` and forward special square-integrability `5eece9e8`): no module
  of the closure states, proves or imports any of these. The closure has no
  segment, socle, head, exhaustion, tempered or square-integrability module.
  Its only `Classification` modules are `Supercuspidal`,
  `SupercuspidalContragredientAux` and `SupercuspidalContragredientStatement`:
  the supercuspidality predicate (vanishing Jacquet coinvariants), class
  packaging, invariance under equivalence, conjugated coinvariants and
  admissibility/irreducibility transfer through contragredients, plus an
  unproved duality proposition. They contain no classification or
  exhaustion theorem and no theorem used here depends on them
  mathematically. The filtration modules are generic Jordan–Hölder and
  length statements about subrepresentation lattices, entering only through
  `ProductVanishing`.
- Detection-unit restrictions: no Ze80 §5.4 reduction or
  strong-indecomposability conclusion (`ff4738d8`), and no two-supercuspidal
  product conclusion (`TwoSupercuspidalNonadjacentProductIrreducible`,
  `3c9849a4`; `TwoSupercuspidalProductStructure`, `ab61f565`). The detection
  proof in the closure is the general BZ77 one that the objective permits.
- Nonadjacent-consumer and BZ77-only restrictions: no individual
  special-head or segment-socle existence (`67279e36`, `4ca79bbd`), no
  adjacent commutation (`e3634665`, `cded83f3`), no segment Jacquet formula
  (`SegmentFullJacquetFormula` / `ed48ae06` and its proof successor,
  `SegmentHeadJacquetFormula` / `55ad1e10`, `SegmentSocleJacquetFormula` /
  `b95105c6`, `SegmentSpecialJacquetExponentNormFormula` / `92aea10f`), no
  Ze80 §3.5 or §9.6 derivative formula, no segment-socle part of
  `8e5b4563`, no Ze80 4.2, 9.3 or 9.7 result, and no classification or
  exhaustion theorem. Every derivative result used (minus exactness,
  4.14(a) with its 4.13(b) inputs, detection, the `Φ̂⁺` constructions,
  Ze80 5.1 (1) ⇒ (3), the lower half of 5.3) is general BZ77/Ze80 §5
  derivative theory with an accepted, published proof, as required by the
  operator conditions of `bd71b9185aab5d6eafffb7891bd3a3ca`.
- Shared upstream restrictions of `3238f371` revision 2 and `2e5183b1`
  revision 2: none of `UnlinkedSegmentSocleProductIrreducible`,
  `LinkedSegmentSocleReverseProductStructure`,
  `LinkedSegmentSoclePairReducible` (`23e98d90`, `a55c4267`, `8fa9f68b`),
  `JuxtaposedSegmentSocleReverseProductStructure`,
  `LinkedSegmentSocleReverseProductQuotientHom` (`7ff2a1e9`),
  `TwoSegmentSocleCommutation` (`426911b4`, `66e3b87c`) or
  `LinkedSegmentSocleGluing` (`c84cd52c`, `6780b79c`) is in the closure or
  used. No result of `62de5903` and no
  `Langlands.Whittaker.SupercuspidalCoinvariantFinitenessStatement` is used
  or imported. No general derivative or tensor result is replaced by an
  assumption from a consumer: the only hypotheses of the imported helper
  lemmas (exactness, 4.14(a)) are discharged by their published proofs.
  The GL Leibniz consumer `3238f371` supplies nothing.
- Whittaker-finiteness independence: the closure contains none of
  `Langlands.Whittaker.SupercuspidalCoinvariantFinitenessStatement`,
  `IrreducibleCoinvariantFinitenessStatement` (`5ab445dc`) or
  `LeviCuspidalCoinvariantFinitenessStatement` (`3ff5c8fb`). Its only
  Whittaker modules are `Representation.Whittaker.Algebraic`,
  `.GeneralLinear` and `.Iwasawa` (characters and the Iwasawa
  decomposition). No mirabolic finite-length result of task `5428fe2c` is
  used or imported; `Category.Basic` only defines finite length.
- Permitted-input conditions:
  - Exactness is used only through the accepted, published proof
    `Mirabolic.minusExactness` (`d307cd07`). Its task `b65bc667` was neither
    resumed, replaced nor bypassed, and minus exactness is not reproved
    here. `GeneralLinearDerivativeExactnessStatement` is not used.
  - BZ77 4.14(a) is used only through the accepted, published proof
    `leftMixedProductDerivative` (`e99bbe1b`) of the statement arranged by
    `f9454f68`, inside the proof of the main theorem. That proof uses
    4.13(b) only through the published proofs of the corresponding clauses
    of task `6cd54f76` (statement task `763a8cf3`) listed above.
    `RestrictedProductLevel.level_leftMixed_le` is used only with that
    discharged `hLD`; no theorem of this module has `hLD` as a premise.
  - The highest-layer statement `MirabolicHighestLayerStatement` (`3826dc7b`)
    is neither imported nor used.
  - Ze80 5.1, the construction of `Φ̂⁺`, the BZ77 §3.2 adjunctions, the
    product embedding for `Φ̂⁺` and the boundary cases are proved in this
    task's published units or in this module; the comparison
    `ρ × Ψ⁺(θ)` versus `Ψ⁺(ρ × θ)` and product nonvanishing are not needed
    (see "Differences from the source").
  - The other statement-only modules in the closure
    (`MixedProductDerivativeStatement` apart from the proved 4.14(a),
    `MirabolicProductMinusCompatibilityStatement` apart from the proved
    clauses, `MirabolicProductRestrictionStatement`,
    `MirabolicMinusExactnessStatement`,
    `MirabolicDerivativeDetectionStatement` and the other `…Statement`
    modules) are targets, not proved inputs; no lemma used here takes an
    unproved one as a hypothesis.
- Consumers: the 4.14(a) proof's audit records that it does not depend on
  this task, on Ze80 6.2 `b711af72` or on the GL Leibniz task `3238f371`,
  so there is no circularity. `RestrictedProductLevel` is a consumer of
  4.14(a), used here as the objective allows.
- Run controls: no operator-paused task was resumed or contacted; Worker
  127 was not contacted.

Credit: the Lean proof of this module and its Markdown are by Worker 1129;
Worker 749 coauthored the task's lower units (the `Φ̂⁺` modules and
`MirabolicDerivativeUnitInjective`) on which step 4 and step 5 rest. The
authors of imported published modules are credited in those modules.
