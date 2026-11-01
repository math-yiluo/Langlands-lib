# Mixed products and normalized mirabolic minus functors

Authors: Worker 499 and Worker 837.

This module proves the unchanged published proposition
`Langlands.Derivative.MirabolicProductMinusCompatibilityStatement.{uF,uV} F T`
from `Langlands.Representation.Derivative.MirabolicProductMinusCompatibilityStatement`.
The entry theorem is

```lean
theorem Langlands.Derivative.mirabolicProductMinusCompatibility
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    Langlands.Derivative.MirabolicProductMinusCompatibilityStatement.{uF,uV} F T
```

It assembles the six independently proved clauses of the actual normalized
minus compatibilities in BZ77 Proposition 4.13(b,c), including both
source-rank-one boundaries. Its proof is conjunction introduction applied
to the six named clause theorems. All comparison maps, their naturality,
the inverse maps and the short exact sequence come from those clause
proofs; none is assumed from a proposition definition.

## Original source and derived assembly

The registered original is I. N. Bernstein and A. V. Zelevinsky, *Induced
representations of reductive p-adic groups I*, Ann. Sci. ENS (4) 10 (1977),
441–472, source ID `bernstein-zelevinsky-1977-induced-i`. The retained PDF is
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`,
SHA256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The source passages and their page images were read during this task:

| Passage | Printed pages; one-based PDF pages | Correspondence |
| --- | --- | --- |
| §1.8 | 444–445; 5–6 | Positive-half covariance for induction and inverse-half normalization for localization. |
| §§3.1–3.2 | 450–451; 11–12 | The mirabolic radical, trivial-character `Ψ⁻`, and nontrivial last-coordinate-character `Φ⁻`. |
| §4.12 | 456–458; 17–19 | Binary GL product and the left and right mixed products; case (III) includes its epsilon factor. |
| Proposition 4.13(b,c) and the following sentence | 458; 19 | The minus comparisons, the right short exact sequence, functoriality of the maps and the source's `P_0 = ∅` boundary convention. |
| §4.14 | 458; 19 | Context for subsequent derivative computations, which are not inputs to this proof. |
| §7.2 | 471; 32 | The source's orbit/localization proof route; the component Markdown explains the concrete implemented routes. |

A bounded search of the project, Library and literature filenames and notes
found no BZ77-specific erratum entry. This records the scope of that search
and is not a global assertion about errata.

The formal conjunction, natural functor packaging, kernel transports and
rank adapters are derived internal content. The component proofs compute
the actual tensor quotients, induction spaces, orbit pieces, Haar factors
and intertwiners. BZ77's displayed formulas are source correspondence,
not assumed comparison theorems. No Ze80 segment formula is used.

## Parameters, ranks and normalizations

The theorem quantifies arbitrary `p`, its primality instance, the actual
`F : PadicField.{uF} p`, and the supplied `T : F.TopologicalData`, with
independent universes `uF,uV`. All six clauses use `letI := T.topology`.
Inputs are arbitrary `SmoothRep.{0,uF,uV} ℂ` objects. Products have carrier
universe `max uF uV`; minus functors and rank pullbacks preserve the carrier
universe of their argument. Every `Φ⁻` clause quantifies all bundled
`UnitaryAdditiveCharacter` inputs, which include continuity and
nontriviality. There is no additional hypothesis of admissibility,
irreducibility, finite dimension, finite length, genericity, a chosen
vector or unit, a canonical topology, universe saturation or a
theorem-valued comparison.

Write `K=k+1>0`. The Library uses `mirabolic r F.Carrier = P_(r+1)(F)`.
Thus

```text
psiMinus T r     : P_(r+1) → GL_r,
phiMinus T ψ r   : P_(r+2) → P_(r+1).
```

For either mixed product of shape `(K,r)`, the result is on `P_(K+r+1)`.
The `leftPhiProduct` and `rightPhiProduct` functors retain
`mirabolicRankCast T (Nat.succ_add k r)`, identifying
`(k+1)+r = (k+r)+1`, before ambient Phi-minus. For source `P_(r+2)`,
the lower mixed products in `leftPhiExpected` and `rightPhiSubobject`
retain the cast `Nat.succ_add k r` and land on `P_(k+r+2)`.
Their corresponding middle Phi product uses `Nat.succ_add k (r+1)`.

The right-Psi target retains
`generalLinearRankCast T (Nat.add_comm r (k+1))`.
The right-Phi quotient retains
`mirabolicRankCast T (Nat.add_comm r k)` after applying
`(psiMinus T r).prod (generalLinearRestriction T k)` and the left
mixed product of shape `(r,k)`. These are actual equality pullbacks on
objects and morphisms, not suppression of ranks or interchange of factors.

Both source-rank-one boundaries use `r=0`. Only the group `GL_0(F)` is
subsingleton; representations of it have arbitrary vector-space carriers.
In particular the right-Psi and right-Phi boundary proofs retain the
entire `Ψ⁻τ` carrier and its actual input map. No positive-rank GL input
is replaced by a unit or by a rank-zero input. No `P_0` is constructed,
and Phi-minus is never applied to `P_1`. Zero objects, repeated factors
and arbitrary multiplicities are included.

The products are precisely `T.binaryNormalizedProductFunctor`,
`T.leftMixedProductFunctor` and `T.rightMixedProductFunctor`. Their
positive-half inducing covariance, the case (III) epsilon factor, and
the inverse-half determinant characters of both minus functors remain
present. The component proofs establish the exact scalar identities
after quotient and Haar transport; no residual scalar or character
twist is omitted.

## The six proof inputs and implemented maps

All clause names in this section are in
`Langlands.Derivative.MirabolicProductMinus`, and all module names are
under `Langlands.Representation.Derivative`. The entry module imports
the six clause modules directly and applies their theorems in the
unchanged conjunction's order.

1. **`leftPsiCompatibility`, module `MirabolicProductMinusLeftPsi`.**
   For every `k,r`, this constructs
   `Ψ⁻(ρ × τ) ≅ ρ × Ψ⁻τ`, naturally in both inputs. At positive source
   index, `leftPsiInductionEquiv` computes the normalized radical
   coinvariants as actual compact induction. The section subgroup is
   the binary parabolic; the full tensor quotient coefficient has its
   two projected blocks and positive binary half modulus. The published
   `binaryPositiveCompactEquivOf` identifies compact and actual binary
   induction, using proved compactness of the parabolic quotient.
   At `r=0`, `leftPsiZeroEquiv` keeps the full tensor carrier.
   `SmoothRep.mkIso` and `NatIso.ofComponents` package the proved
   equivariance, inverses and both-input naturality.

2. **`leftPhiCompatibility`, module `MirabolicProductMinusLeftPhi`.**
   For every `ψ,k,r`, this constructs
   `leftPhiProduct T ψ k (r+1) ≅ leftPhiExpected T ψ k r`.
   `leftPhiCompatibilityIso` composes the actual higher-product
   identity-localization isomorphism, explicit stabilizer localization,
   the full normalized identity/source comparison, the identical lower
   expected coefficient model, and the inverse host-rank comparison.
   The published two-orbit restriction sequence and character-localization
   right exactness identify the higher product with the identity piece:
   the cycle piece vanishes because its terminal character is nontrivial
   while its coefficient acts trivially there. The normalized identity
   piece is computed by the published character-stages, ambient twist,
   tensor-quotient and compact-induction comparisons. Every coefficient
   map is the tensor of the first input map with the actual source-Phi
   quotient map. Full faithfulness of `SmoothRep.toRep` lifts the
   composite and its inverse back to the exact smooth host functors.

3. **`leftPhiBoundary`, module `MirabolicProductMinusBoundary`.**
   For source `P_1`, the case (II) subgroup is the entire mirabolic group
   and its projection kills the radical. The radical therefore acts
   trivially on the actual induced product. Choose a radical element
   with nontrivial `θ_ψ` value. The full Phi quotient relation makes
   every quotient vector zero, giving the required subsingleton carrier.
   The relevant rank cast is definitionally the identity.

4. **`rightPsiCompatibility`, module `MirabolicProductMinusRightPsi`.**
   This constructs `Ψ⁻(τ × ρ) ≅ Ψ⁻τ × ρ` at every source rank.
   At positive source index, the explicit kernel intersection is the
   source radical, its tensor coinvariants are `Ψ⁻τ ⊗ ρ`, and the
   published split-stages integral comparison produces compact induction
   from the binary parabolic. Its quotient Haar ratio is `|det D|`.
   The proved real-power identity keeps the ambient/source minus
   normalizations and case (III) covariance. Compact-induction rank
   transport and the binary compact comparison give the actual target.
   At `r=0`, the case (III) subgroup meets the radical trivially; the
   twisted split-kernel integral and evaluation identify both complete
   carriers with the full tensor. The comparison is natural for both
   arbitrary input maps and reinstates the stated GL rank pullback.

5. **`rightPhiShortExact`, module `MirabolicProductMinusRightPhi`.**
   For source `P_(r+2)`, `mirabolicMixedOrbitCoverage` supplies the
   ordered cycle/identity two-orbit enumeration.
   `rightPhiCyclePiece_iso` identifies the normalized cycle piece with
   `rightPhiSubobject`, and `rightPhiIdentityPiece_iso` identifies the
   normalized identity piece with `rightPhiQuotient T k (r+1)`.
   `rightPhiShortExact_of_pieces` applies the published localized
   two-orbit Mackey sequence, the full ambient normalization and these
   two natural isomorphisms.

   More explicitly, write the unnormalized Mackey maps as `i₀,q₀`,
   whisker with the actual right inducing-coefficient functor and the
   ambient inverse-half twist to get `i₁,q₁`, and write the three
   identifications with the host terms as `eA,eB,eD`. The maps supplied
   to the smooth category are the lifts of
   `eA.inv ≫ i₁ ≫ eB.hom` and `eB.inv ≫ q₁ ≫ eD.hom`.
   Thus they are actual natural transformations on the full product
   category. `exact_comp_isos`, `exact_whiskerRight_repTwist` and
   `exact_liftNatTrans` preserve component injectivity, equality of the
   linear-map range and kernel, and component surjectivity. The source
   is the right mixed product `(Φ⁻τ) × ρ`; the quotient is the left
   mixed product `(Ψ⁻τ) × (ρ|P_K)`. All three terms land on
   `P_(k+r+2)` with their proved rank maps.

6. **`rightPhiBoundary`, module `MirabolicProductMinusRightBoundary`.**
   At source `P_1`, the case (III) inducing subgroup has trivial
   intersection with the radical. A `θ_ψ`-twisted split-kernel integral
   gives the complete source quotient and its section action. Its
   inverse Haar modulus `|det l|` cancels the ambient inverse-half and
   case (III) inverse-half factors. Both source and target identify
   naturally with the entire tensor `τ ⊗ ρ`, with action `1 ⊗ ρ(l)`.
   The target uses the full `GL_0` carrier of `Ψ⁻τ`. Reinstating the
   mirabolic rank pullback yields the required natural isomorphism.

The final Lean proof introduces no new comparison hypothesis and
performs no additional mathematical reduction. Conjunction introduction
retains every quantified rank, character, object, morphism and exactness
condition in the six unchanged proposition definitions.

## Direct and transitive mathematical dependency audit

The six direct imports are the clause modules just named. Each clause
has an independently accepted and published proof. Their paired
Markdown gives the declaration-level construction and audit; the
following table checks the combined proof against every inherited
restriction, including transitive use.

| Condition | Actual combined dependency finding |
| --- | --- |
| Exact target and unconditional scope | The theorem applies the six proved clauses, in order, to the unchanged published conjunction. The proposition module supplies the target and actual functor definitions; none of its unproved propositions supplies evidence. There are no extra hypotheses. |
| Actual natural maps and quotients | The first, second, fourth and sixth clauses supply natural isomorphisms with full intertwiners and inverses. The fifth supplies the actual natural injection and quotient with pointwise short exactness. The third proves zero of the actual quotient carrier. |
| Ranks and full carriers | The actual GL and mirabolic rank pullbacks listed above occur in the component constructions. Both `r=0` right clauses retain the full GL-zero carrier and both input maps. Every positive GL input has rank `k+1`. |
| Exact normalizations | Published determinant characters, full tensor quotients, ambient/source inverse-half twists and case (III) epsilon are used. The split-kernel and stages comparisons retain the proved Haar moduli, and the component scalar identities eliminate the complete residual twist. |
| Generic induction and localization | Published compact induction, transitivity, character twist, compact-induction transport, full relation-span localization transport and character-stages comparisons supply the lower equivalences. Their continuity, subgroup, smoothness, measure and character hypotheses are proved at the actual supplied topology. No bijectivity or comparison premise remains. |
| Parabolic compactness | The binary compact comparison uses proved compactness of the actual parabolic quotient, from elementary integral-subgroup Iwasawa reduction and compactness. It assumes no representation finiteness or classification. |
| Two-orbit sequence and exactness owners | Published closed-subgroup Mackey filtration, its two-step exact sequence, right exactness and character-localization exactness are reused. Coverage is the published elementary matrix-orbit proof. The separate restriction-sequence and exactness owners are not duplicated, and no BZ77 4.13(a) conclusion is assumed. |
| Plus functors and adjunction | `MirabolicPlus` enters the right-Phi import closure through `MirabolicPhiMinusMackey`. Its mathematical use is restricted to the elementary character `thetaPlus` and its laws. `plusPhiLocalization` is a minus character quotient on `Q`, not a plus representation functor. No `phiPlusUnnormalized`, `psiPlusUnnormalized`, plus-functor comparison or adjunction conclusion supplies an input. The imported `OpenSubgroupAdjunctionClause` is only a proposition definition. |
| BZ77 4.13(d) and general Leibniz | No submodule-detection theorem, general Leibniz proof or general derivative-filtration theorem is used. The lower `Filtration.Definitions` and two-orbit `RepFunctorFiltration` constructions do not assert those consumer conclusions. |
| Segment derivative and Jacquet formulas | No segment derivative result, Ze80 §3.5 or §9.6 formula, full/head/socle Jacquet formula or special Jacquet exponent formula is used, directly or transitively. |
| Individual segment existence | No individual special-head/reverse-socle or segment-socle/reverse-head existence conclusion, successor or downstream consequence is used. |
| Linked and unlinked socle consumers | No unlinked product irreducibility, linked reverse-product structure, linked-pair reducibility, juxtaposed reverse-product structure or reverse-product quotient homomorphism supplies an input. |
| Segment product, commutation and gluing | No segment-socle product irreducibility, adjacent swap, two-segment commutation, linked-segment gluing, or Ze80 4.2 or 9.7 criterion is used. |
| Special-head criterion and generic uniqueness | No special-head product irreducibility or generic segment-product uniqueness conclusion, parent task, successor or consequence is used. |
| Ordered existence, coverage and exhaustion | No ordered multisegment-socle or strong-head existence, socle or special-head multisegment exhaustion, quotient coverage or ordered conversion supplies an input. |
| Analytic, tempered and square-integrable classification | No analytic segment classification, forward special essential square-integrability, tempered uniqueness, square-integrable Langlands classification, square-integrable or regular exhaustion, or Ze80 9.3 conclusion supplies an input. |
| Two-supercuspidal consumers | Neither nonadjacent-product irreducibility nor two-supercuspidal product structure or its full-product assembly supplies an input. None of the parent six-statement conclusions (b),(d),(e),(f) is used. |
| Supercuspidal and arbitrary-character finiteness | No supercuspidal coinvariant-finiteness statement, all-character single-block conclusion, arbitrary-character finiteness result, successor or downstream consequence supplies an input. |
| Other Whittaker finiteness | No irreducible or Levi-cuspidal coinvariant-finiteness conclusion, their parent/proof tasks, or the prohibited mirabolic finite-length route is used. Compact averaging, compatible quotient measures and compact local sections are lower constructions and supply no such finiteness conclusion. |
| Imported higher-level interfaces | `Classification.Supercuspidal` and its contragredient interfaces enter through lower compact-orbit/local-section infrastructure. Whittaker and Rankin–Selberg modules supply elementary character, coefficient, cutoff, measure and unimodularity constructions. No excluded classification, segment or finiteness theorem is imported from them as a mathematical premise. |
| Proof status and frozen inputs | Every imported pair is published and unchanged. The target's pair and its imports are unchanged. No draft, pending candidate, citation, source formula, proposition definition or consumer task is used as a proved comparison. |
| Run controls and ownership | Worker 127's operator pause, Worker 8's suspension, Worker 114's hold and all current suspensions remain binding. No suspended worker was asked to resume. The final theorem adds no rank-zero input GL extension; that extension remains with the separate all-rank owner. |

The exclusions in these rows cover each mathematical conclusion, proof
successor and downstream consequence of the named tasks in the inherited
contract. The identifier coverage below makes that audit explicit.

| Task identifiers in the inherited scope | Covered exclusion or scope |
| --- | --- |
| `23e98d90-6055-4e35-91a9-b0f5d8a84961`, `a55c4267-7e3a-43f6-8bb1-ce319e1d0aa9`, `8fa9f68b-fa1b-431a-97f6-5b163964d1fc` | Unlinked irreducibility, linked reverse-product structure and linked-pair reducibility. |
| `7ff2a1e9-89dc-439e-a861-a567b3db92bf` | Juxtaposed reverse-product structure and linked reverse-product quotient homomorphism. |
| `2ae5cbe5-0701-4509-88a0-db8cbeb35be4` | Segment-socle product irreducibility. |
| `e3634665-571b-4852-9f4c-bab8a1053434`, `cded83f3-df9c-4018-bc61-dc54f5c1f9ab` | Adjacent unlinked-socle swap and proof successor. |
| `426911b4-6620-413f-8065-04b25287f3bd`, `66e3b87c-647e-41e4-af18-df4d436765f0` | Two-segment socle commutation. |
| `c84cd52c-3ff3-4024-be50-8b84dd480888`, `6780b79c-9526-46aa-b8b4-00377d68b1ea` | Linked-segment socle gluing. |
| `23189526-80b0-4828-a6d4-7ebec2cbeef5`, `f3a69bc8-7312-4f82-8a7d-ea3c8188cb63` | Ordered multisegment-socle existence and socle exhaustion. |
| `67279e36-f3c2-42e3-9302-11729784042e`, `4ca79bbd-589e-476b-9f65-661e799984b5` | Individual special-head/reverse-socle and segment-socle/reverse-head existence. |
| `aca8805b-054f-4d56-8045-12db7f623404`, `5eece9e8-7f6b-4ea9-abea-a1f9f1b8c807` | Analytic segment classification and forward special essential square-integrability. |
| `3bfb61fa-1129-4fc9-83fd-7fcfec22106e`, `ebea9a8a-9b21-4208-aa31-98c2dea1f8a3` | Special-head multisegment exhaustion and ordered strong-head existence. |
| `20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584`, `8252833d-c269-41a9-824c-5879e531b23b` | Quotient coverage and ordered conversion. |
| `52e97845-36bb-457d-b76f-70753334b88c`, `1cb45da2-7007-4351-a694-594fb148b8d1` | Tempered uniqueness and square-integrable Langlands classification. |
| `cd8ab97c-0b78-4bce-97c4-d307a28159a4`, `bf433f0a-921a-428c-b0c0-6475438125ac` | Square-integrable and regular exhaustion. |
| `8364e73f-14ec-4d14-8f2b-1555a7c1ce95`, `30341ae4-65f2-4a0e-9283-763db01a409e` | Special-head product criterion and generic segment-product uniqueness. |
| `ed48ae06-964c-4c84-9e62-978f5a953ca7`, `55ad1e10-62d8-46b7-a081-909ef0056426`, `b95105c6-f8bb-4641-ae53-2f49d1e7f034`, `92aea10f-62ac-4e0b-bd4a-9a80909797c5` | Full, head, socle and special-exponent segment Jacquet formulas. |
| `3c9849a4-a6c0-43ac-9982-d15ed76bf1e9`, `ab61f565-1427-4746-ba77-46097563e962` | Two-supercuspidal nonadjacent irreducibility and full-product structure/assembly. |
| `62de5903-b616-4b5c-88eb-a066b77c5467` | All-character single-block finiteness. |
| `5ab445dc-d2b4-4072-80d1-6370870a4a26`, `3ff5c8fb-397c-4345-bcb3-5d98a0993d18`, `5428fe2c-013c-482d-aa6e-7df43e7191aa` | Irreducible/Levi-cuspidal coinvariant finiteness and the prohibited mirabolic finite-length route. |
| `2e5183b1-01e9-44fb-b26c-f4521a25c7c7` | Source of the inherited derivative-task restrictions. Its unproved final derivative conclusion is not a proof input; only the independently published lower results listed here are used. |

The source scan covers all 38 identifiers in that inherited-scope union
and all 24 named consumer declarations, including
`SupercuspidalCoinvariantFinitenessStatement`,
`IrreducibleCoinvariantFinitenessStatement` and
`LeviCuspidalCoinvariantFinitenessStatement`. None occurs in the Lean code
of the entry or its project import closure. The scan also finds no proof
holes, new axioms, native evaluation or kernel-bypass commands. The
mathematical-use audit above is separate from this textual check; absence
of a symbol alone would not establish independence.

Declaration inspection reports only the standard logical axioms
`propext`, `Classical.choice` and `Quot.sound`, and the independent
universe parameters `uF,uV`. Compilation and inspection are development
verification; the final proof requires its own independent review and
exact-target validation.

## Complete project import closure

The following 277 project modules are the complete transitive
project import closure of the six direct imports, including those direct
imports and the unchanged target statement module. The entry module itself
is the new proof and is not counted among its imports. Each listed module
has a nonempty Lean/Markdown pair.

The audit base is Library commit `a76eaf5aaac38487c19b4cf2e7c9bd64e2493518`.
All 277 published pairs (554 files) are byte-identical
to that commit and have been checked against its file manifest.
Every imported pair is published. The complete target statement pair
and all of its imports are included in this unchanged-pair check.

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
Langlands.Representation.Derivative.MinusVanishing
Langlands.Representation.Derivative.MirabolicCharacter
Langlands.Representation.Derivative.MirabolicDeterminant
Langlands.Representation.Derivative.MirabolicLatticeBox
Langlands.Representation.Derivative.MirabolicMinus
Langlands.Representation.Derivative.MirabolicMinusExactnessProof
Langlands.Representation.Derivative.MirabolicMinusExactnessStatement
Langlands.Representation.Derivative.MirabolicMixedOrbitCharacters
Langlands.Representation.Derivative.MirabolicPhiMinusMackey
Langlands.Representation.Derivative.MirabolicPlus
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
Langlands.Representation.Derivative.MirabolicProductMinusRightBoundary
Langlands.Representation.Derivative.MirabolicProductMinusRightPhi
Langlands.Representation.Derivative.MirabolicProductMinusRightPhiAssembly
Langlands.Representation.Derivative.MirabolicProductMinusRightPhiCycle
Langlands.Representation.Derivative.MirabolicProductMinusRightPhiCycleCoefficient
Langlands.Representation.Derivative.MirabolicProductMinusRightPhiCycleGroups
Langlands.Representation.Derivative.MirabolicProductMinusRightPhiIdentity
Langlands.Representation.Derivative.MirabolicProductMinusRightPhiIdentityCoefficient
Langlands.Representation.Derivative.MirabolicProductMinusRightPhiIdentityGroups
Langlands.Representation.Derivative.MirabolicProductMinusRightPsi
Langlands.Representation.Derivative.MirabolicProductMinusRightPsiCoefficient
Langlands.Representation.Derivative.MirabolicProductMinusRightPsiGroups
Langlands.Representation.Derivative.MirabolicProductMinusRightPsiZero
Langlands.Representation.Derivative.MirabolicProductRestrictionFactors
Langlands.Representation.Derivative.MirabolicProductRestrictionMackey
Langlands.Representation.Derivative.MirabolicProductRestrictionOrbits
Langlands.Representation.Derivative.MirabolicProductRestrictionTransport
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
Langlands.Representation.Induction.SplitKernelCharacter
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

## External import boundary

The following 125 distinct Lean/Mathlib modules are all direct
external imports encountered while traversing the complete project closure.
They are the external boundary of that closure, not an assertion that
their own transitive dependencies are absent. Those dependencies are
supplied by the pinned environment: Lean
`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b` and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.

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
