# Zelevinsky 6.2 from the lower statements of its proof

Module
`Langlands.Representation.Classification.SegmentSocleProductHomogeneityAssembly`,
namespace `Langlands.Classification`.

The module has one definition and two theorems.

- `SegmentSocleProductHomogeneityInputs.{uF, uV} F T : Prop` is the
  conjunction of the nine lower propositions listed below, in the order of
  the table. It adds no condition of its own.
- `segmentSocleProductHomogeneity_of` proves the published target
  `SegmentSocleProductHomogeneity.{uF, uV} F T` (Zelevinsky 1980, Theorem
  6.2) from these nine propositions, taken as separate explicit hypotheses.
- `segmentSocleProductHomogeneity_of_inputs` is the same result with the
  conjunction `SegmentSocleProductHomogeneityInputs.{uF, uV} F T` as its
  single hypothesis. It splits the conjunction and applies
  `segmentSocleProductHomogeneity_of`.

These are conditional results: neither is the unconditional proof
`segmentSocleProductHomogeneity`. That proof, in
`SegmentSocleProductHomogeneityProof`, applies
`segmentSocleProductHomogeneity_of` to published proofs of every
hypothesis.

The target says: for every unitary additive character `ψ`, every `N`, and
every segment-product datum `d` of rank `N + 1` with segment socles
(`d.HasSegmentSocles`) such that
`(d.segments j).base ≠ ((d.segments i).last).twist 1` whenever `i < j`, the
product `d.induced = ⟨Δ_1⟩ × ⋯ × ⟨Δ_r⟩` is homogeneous
(`IsGeneralLinearHomogeneous T ψ d.induced`: its restriction to the
mirabolic subgroup is homogeneous). This is Ze80 6.2 with
`Δ_i = [ρ_i, ρ'_i]` and the condition `ρ_j ≠ ν ρ'_i` for `i < j`.

## Hypotheses

None of these is proved here. All are published Library propositions.

| Hypothesis | Proposition | Module | Source |
| --- | --- | --- | --- |
| `hE` | `Mirabolic.MinusExactnessStatement.{uF, max uF uV} F T` | `Derivative.MirabolicMinusExactnessStatement` | exactness of `Ψ⁻`, `Φ⁻` (BZ77 3.2) |
| `hS` | `MirabolicProductMinus.RightPhiShortExact.{uF, max uF uV} F T` | `Derivative.MirabolicProductMinusCompatibilityStatement` | BZ77 4.13(c) |
| `hB` | `MirabolicProductMinus.RightPhiBoundary.{uF, max uF uV} F T` | `Derivative.MirabolicProductMinusCompatibilityStatement` | BZ77 4.13(c), `P_1` boundary |
| `hD` | `RightMixedProductPhiMinusDetection.{uF, max uF uV} F T` | `Derivative.MixedProductDerivativeStatement` | BZ77 4.13(d) |
| `hLD` | `LeftMixedProductDerivative.{uF, max uF uV} F T` | `Derivative.MixedProductDerivativeStatement` | BZ77 4.14(a) |
| `hH` | `LeftMixedProductHomogeneity.{uF, max uF uV} F T` | `Derivative.LeftMixedProductHomogeneityStatement` | Ze80 5.3 |
| `h35` | `SegmentSocleDerivatives.{uF, uV} F T` | `Classification.SegmentSocleDerivativesStatement` | Ze80 3.5 |
| `hF` | `SegmentSocleProductHighestDerivative.{uF, uV} F T` | `Classification.SegmentSocleDerivativesStatement` | highest derivative of a segment-socle product (Ze80 3.5 with BZ77 4.6) |
| `hC` | `CuspidalProductMirabolicSupportShift.{uF, uV} F T` | `Classification.CuspidalProductMirabolicSupportShiftStatement` | BZ77 4.7(b), as used in Ze80 4.4–4.5 |

All module names are under `Langlands.Representation`. The statements of
`hH` and `hC` were published after the modules
`SegmentSocleProductHomogeneityInduction` and `SegmentSocleProductCaseTwo`
were written. Those modules take the bodies of these propositions at a
fixed `ψ` as inline hypotheses. This theorem passes the instances `hH ψ` and
`hC ψ`.

`hS` and `hB` are the fifth and sixth conjuncts of the published
`MirabolicProductMinusCompatibilityStatement` (BZ77 4.13(b,c)). Only these
two conjuncts are used, so only these two are assumed.

BZ77 4.13(a) is not a hypothesis. The theorem uses the published proof
`Langlands.Derivative.mirabolicProductRestriction F T`, at universes
`uF, max uF uV`, from module `Derivative.MirabolicProductRestriction`.
It proves `MirabolicProductRestrictionStatement`, the premise
`hR` of `homogeneous_of_caseTwo`.

## Proof

Fix `ψ`, `N`, `d`, `hd` and the endpoint condition. Since `d` has rank
`N + 1`, it has at least one segment, so `d.length = (d.length - 1) + 1`
(a datum of length `0` has rank `0` by `d.degree_sum`). The theorem then
applies `SegmentSocleProductHomogeneityInduction.homogeneous_of_caseTwo` with
`k = d.length - 1` and rank `N + 1`. Its hypotheses are `hE`, `hD`, `hS`,
`hB`, the published proof of BZ77 4.13(a), `hLD`, `hH ψ` and `h35`. Its
Case 2 premise `hC2` is
`SegmentSocleProductCaseTwo.caseTwoExclusion` with `hE`, `hLD`, `hH ψ`,
`hC ψ` and `hF`.

`segmentSocleProductHomogeneity_of_inputs` destructures its hypothesis into
`hE, hS, hB, hD, hLD, hH, h35, hF, hC` and applies
`segmentSocleProductHomogeneity_of`.

## Provenance

Ze80 §6.3 (`zelevinsky-1980-induced-ii`, printed pp.188–189) proves
Theorem 6.2 by the argument of BZ77 4.15
(`bernstein-zelevinsky-1977-induced-i`, printed pp.458–459), with `ρ_1`
replaced by `⟨Δ_1⟩`, BZ77 4.4 by Ze80 3.5, Case 1 via Ze80 5.3, and Case 2 via
"the reasoning of 4.5". The two cited modules formalize that argument (see
their Markdown); this theorem only combines them. The hypothesis list, and
so the definition `SegmentSocleProductHomogeneityInputs`, is internal
derived material: it records the lower results that the Lean proof of those
modules uses. The definition is Lean packaging with no counterpart in the
literature. The Ze80 3.5 statement `SegmentSocleDerivatives` and
the highest-derivative statement `SegmentSocleProductHighestDerivative` are
used only as hypotheses; Ze80 6.3 uses Ze80 3.5 as an input.

## Conventions

`{p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}` and `T : F.TopologicalData`
are fixed. `SegmentSocleProductHomogeneityInputs` takes `F` explicitly, like
the target and the lower propositions. In the target, representations of `GL_n` have carriers in
`Type (max uF uV)`. The lower propositions about mirabolic and mixed products
are therefore used at universes `uF, max uF uV`. The segment statements `h35`,
`hF` and `hC` are used at `uF, uV`, since they already put their
representations in `Type (max uF uV)`.

## Import audit

The direct imports are `Classification.SegmentSocleProductCaseTwo` and the
published modules `Derivative.MirabolicProductMinusCompatibilityStatement`,
`Derivative.LeftMixedProductHomogeneityStatement`,
`Classification.CuspidalProductMirabolicSupportShiftStatement` and
`Derivative.MirabolicProductRestriction`.

`SegmentSocleProductCaseTwo` and `SegmentSocleProductHomogeneityInduction`
are published. They use
the published Classification helper modules
`SegmentProductCuspidalEmbedding`, `SegmentProductSplit` and
`SegmentContentShift`. The
import audit in `SegmentSocleProductHomogeneityInduction.md` covers those
five modules. It also covers the five published Derivative helpers
(`LevelCalculus`, `ProductVanishing`, `RestrictionBridge`, `RightMixedLevel`,
`RestrictedProductLevel`).

On Library commit `5e4a58e8`, the transitive project import closure of this
module has 601 modules. The other
600 are published, and the copies of their Lean and Markdown files checked here
are byte-identical to that commit. The closure of the two modules
`SegmentSocleProductCaseTwo` and `SegmentSocleProductHomogeneityInduction`
has 585 modules. This module adds 16: itself and the following 15 published
modules.

- The statement modules `Derivative.LeftMixedProductHomogeneityStatement`
  and `Classification.CuspidalProductMirabolicSupportShiftStatement`. They
  only define propositions, which are assumed here as `hH` and `hC`.
- The published proof of BZ77 4.13(a): `Derivative.MirabolicProductRestriction`
  and its helpers `MirabolicProductRestrictionCasts`, `…Factors`, `…Mackey`,
  `…Orbits`, `…Stabilizers` and `…Transport`.
- Modulus facts used by that proof: `Group.GL.MirabolicModularCharacterStatement`,
  `Group.GL.MirabolicModularCharacterProof`, `Group.GL.MirabolicModulusStatement`,
  `Group.GL.MirabolicModulusProof`, `RankinSelberg.GeneralLinearUnimodularity`
  and `Analysis.Local.ModularCompactAverage`.

The closure of `Derivative.MirabolicProductRestriction` alone has 160
modules. Its only Classification modules are `Classification.Supercuspidal`,
`SupercuspidalContragredientAux` and `SupercuspidalContragredientStatement`.
It contains no segment, socle or multisegment module.

So the closure contains no proof module for the conclusions excluded for
this proof: ordered-socle existence, socle exhaustion, analytic segment
classification, segment-socle product irreducibility, the final segment-socle
irreducibility criterion, `AdjacentUnlinkedSegmentSocleSwap`,
`TwoSegmentSocleCommutation`, the special-head criterion, special-head
exhaustion and existence, quotient coverage, tempered-block uniqueness,
`SquareIntegrableLanglandsClassification`, square-integrable and regular
exhaustion, `GenericSegmentProductUniqueness`, ordered special-segment
conversion, and special-segment essential square-integrability. The
statement-only classification modules in the closure are listed in
`SegmentSocleProductHomogeneityInduction.md`. None of their propositions is
assumed or proved here.
