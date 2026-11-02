# Derivative support bound for a supplied special head

Author: Worker 357.

This pair defines the unproved proposition
`Langlands.Classification.SegmentHeadDerivativeSupportTruncation.{uF,uV} F T`.
It is a statement for a focused independent proof successor. This module
contains no proof and is not a proved input to the host task
`8364e73f-14ec-4d14-8f2b-1555a7c1ce95`.

The parameters are every prime `p`, actual `F : PadicField.{uF} p`, supplied
`T : F.TopologicalData`, and continuous nontrivial unitary additive character
for `T.topology`. The field universe `uF` and original supercuspidal carrier
universe `uV` are independent. The original segment is
`Δ : T.Segment.{uV,uF}`. Its supplied head and derivative constituents have
carriers in `Type (max uF uV)`. Support classes and the truncating segment
remain in the original universe `uV`.

For any actual representation `π` satisfying the existing strong-head relation
`T.IsSegmentHead Δ π`, every `k ≤ Δ.degree`, and every actual irreducible
subquotient `σ` of `(generalLinearDerivative T ψ Δ.degree k hk).obj π`,
the proposition asks for:

- An actual multiset `s` in the published relation
  `T.IsSupercuspidalSupport σ s`.
- An optional actual segment `A`, with `none` representing the empty support.
- The existing relation `Segment.IsTerminalTruncation A Δ`.
- Equality of the underlying set of `s` with `Segment.optionalSupport A`.

For `some E`, terminal truncation means `E.support ⊆ Δ.support` and
`Δ.last ∈ E.support`. The whole original segment is allowed. The derivative
order zero and top order are included. The conclusion records existence of
a support in the original base universe, rather than a conditional assertion
about supports that might not exist in that universe.

The support multiset is actual, but the equality compares only its underlying
set. The proposition does not determine multiplicities, the relation of
truncation length to derivative order, the number of simple factors, or their
isomorphism classes. It asserts no irreducibility or nonvanishing of the whole
derivative and constructs no equivalence to a truncated head. Its scope is
strictly weaker than the full special-head derivative formula.

## Intended use and remaining proof work

The host's independently compiled private product construction already gives
an actual scalar model for the entire top derivative of every supplied head
product. A generic exact-functor argument would then give irreducibility if
every simple actual subquotient survives that top derivative. That survival
condition is still unproved.

A proof of this bound, followed by the general Leibniz filtration
and actual constituent-support transport, is a possible route to terminal
truncation descriptions for a simple submodule of a highest derivative.
A duality argument would also need an initial-truncation description on
the other side. The published segment-truncation obstruction could then apply
only after establishing the required shifted equality and nonempty support.
This pair establishes none of those steps. In particular, a set-containment
bound without terminal endpoint retention would not meet the existing
combinatorial lemma's hypotheses.

## Provenance and authorized proof boundary

This interface is an internal weakening suggested by the support use
in Zelevinsky 1980, section 9.8, printed pp.199–200. The full formula in
Proposition 9.6, printed p.198, implies such a bound, but is excluded as an
input to this host. The source's proof of 9.6 also uses 8.1 and 9.5, which
do not supply an independent route for this task.

The registered source is `zelevinsky-1980-induced-ii`, SHA256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`,
retained at
`/home/taskhub/central-library/Zelevinsky--Induced representations of reductive p-adic groups II, irreducible representations of GL(n)--1980.pdf`.
The full extracted text of printed pp.198–200 was read again during this
preparation, including the derivative formula's proof and the support step in
§9.8. The published source audit
`notes/henniart/segment-head-independence.md` records the classification
dependencies and previously found no matching errata entry.

The complete trusted operator response
[30144f6f9b59540b88b6d4c1517892d9](/home/taskhub/pilot/correspondence/30144f6f9b59540b88b6d4c1517892d9.md)
to request `7bd9e666c60d53469eff04b2962e1acf` expressly permits a new independent
proof of exactly this support-only statement and its subsequent use. It
clarifies the earlier responses
[bd71b9185aab5d6eafffb7891bd3a3ca](/home/taskhub/pilot/correspondence/bd71b9185aab5d6eafffb7891bd3a3ca.md)
and
[0edda6122ce65ed7ac51603c37473920](/home/taskhub/pilot/correspondence/0edda6122ce65ed7ac51603c37473920.md).
The following conditions apply to the exact proof successor and its use:

- Keep the conclusion exactly support-only. Do not replace it by
  irreducibility of the derivative, an identification with a truncated head,
  a multiplicity assertion or a full derivative formula. If a proof needs
  such a strengthening, stop and seek an operator ruling.
- Use only independently accepted and published general BZ77 derivative
  theory, Gelfand–Kazhdan, the Leibniz rule, Theorem 4.2, the authorized
  general Ze80 3.7(b) comparison and 5.3 infrastructure, and the already
  permitted independent individual-head constructions.
- Exclude Ze80 3.5/9.6, their published proofs, proof successors and circular
  uses. Exclude the full product criterion in either direction and every
  host independence exclusion below.
- Publish this statement before a focused `lean.proof@1` task whose exact
  target is this declaration. Carry the exclusions into that contract.
  Use its eventual theorem only after independent acceptance and Library
  publication.
- Record the complete closure and mathematical proof-dependency audit in
  the proof's Markdown and the host's final Markdown, citing the response.

These are proof and dependency requirements, rather than extra hypotheses
added to the proposition. The permission supplies no proof term.

### Retained exclusions

The prohibition includes each named task's excluded conclusion, its proof
successors, renamings and direct or transitive uses:

| Excluded conclusion | Task or source |
| --- | --- |
| Parent generic special-head product uniqueness | `30341ae4-65f2-4a0e-9283-763db01a409e` |
| Multisegment exhaustion | `3bfb61fa-1129-4fc9-83fd-7fcfec22106e` |
| Ordered strong-head existence | `ebea9a8a-9b21-4208-aa31-98c2dea1f8a3` |
| Quotient coverage | `20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584` |
| Ordered conversion | `8252833d-c269-41a9-824c-5879e531b23b` |
| Tempered uniqueness | `52e97845-36bb-457d-b76f-70753334b88c` |
| Square-integrable Langlands classification | `1cb45da2-7007-4351-a694-594fb148b8d1`, `SquareIntegrableLanglandsClassification` |
| Square-integrable exhaustion | `cd8ab97c-0b78-4bce-97c4-d307a28159a4` |
| Regular exhaustion | `bf433f0a-921a-428c-b0c0-6475438125ac` |
| Full special-head product irreducibility, either direction | `8364e73f-14ec-4d14-8f2b-1555a7c1ce95`, `SegmentHeadProductIrreducibility` |
| Segment derivative formulas and their proofs or successors | Ze80 3.5 and 9.6; the segment-socle part of `8e5b4563-0365-41c7-b134-70f2a0b36292` |
| Full, head or socle segment Jacquet formulas and exponent-norm formula | `ed48ae06-964c-4c84-9e62-978f5a953ca7`, `55ad1e10-62d8-46b7-a081-909ef0056426`, `b95105c6-f8bb-4641-ae53-2f49d1e7f034`, `92aea10f-62ac-4e0b-bd4a-9a80909797c5` |
| Segment-socle product irreducibility, linked structure, gluing, commutation, swaps or socle exhaustion | Including `2ae5cbe5-0701-4509-88a0-db8cbeb35be4`; permitted generic infrastructure is distinguished from these conclusions |
| Analytic segment classification, special square-integrability, two-supercuspidal product irreducibility or structure, and Whittaker coinvariant finiteness | Excluded mathematical conclusions remain excluded |

The isolated independently proved cuspidal-derivative part of
`8e5b4563-0365-41c7-b134-70f2a0b36292` is permitted. The response
`0edda6122ce65ed7ac51603c37473920` also authorizes the general 3.7(b)
comparison through Lemma 4.7(b), 5.3 `leftMixedProductHomogeneity` and the
specified nine generic modules, only after independent acceptance and
publication. Permission for generic infrastructure does not authorize
the introducing tasks' excluded mathematical conclusions.

Only existing definitions are imported here: the actual general derivative,
actual support relation, actual segments, and the optional-truncation
notation. No derivative formula or excluded conclusion is imported or used
as a proof. Compilation of this proposition checks its interface, not its
truth or acceptance.

## Statement closure and development evidence

Terminal development check `d5ad932c-e66d-495b-b923-366612a741f4` compiles
this module with zero errors and warnings. Its inspection reports a
Prop-valued definition, independent `uF` and `uV`, and only `propext`,
`Classical.choice`, and `Quot.sound`. No proof of the proposition is present.

The refreshed recursive inventory is
`.private/notes/worker357-head-derivative-support-import-audit-2026-11-02.json`.
It contains 80 project modules including the new root, and 69 external import
roots. All 79 inherited Lean/Markdown pairs match Library
`46ad94719738ee676dd6e863d6e924cca8fec970` byte for byte, with no missing
module or paired Markdown and no proof-hole or new-axiom occurrence.
The exclusion scan's broad `SegmentHeadDerivative` prefix matches this
root declaration itself. There are no inherited matches. This name scan
checks source inventory; authorization comes from the complete trusted
operator response above.

The three direct imports are:

| Module, prefixed by `Langlands.Representation.` | Content used here |
| --- | --- |
| `Derivative.Iteration` | The actual normalized general-linear derivative functor, including order zero and top order |
| `Classification.SupercuspidalSupport` | Actual constituent and support relations; no support uniqueness assumption |
| `Classification.SegmentTruncationObstructionStatement` | Only its transparent optional-support and terminal-truncation definitions; the obstruction proposition is not assumed |

The only derivative modules in this closure are `Iteration`,
`MirabolicMinus` and `MirabolicCharacter`. They define the functors and their
elementary normalization adapters. The classification modules are
`ConstituentRelations`, `Segments`, `Supercuspidal`,
`SupercuspidalTwist`, `SupercuspidalSupport`, the optional-truncation statement
and this new root. They supply actual relations and notation. This file
contains no application of an unproved statement, segment derivative
formula or classification theorem. In particular, importing the
truncation-notation module is not a proof or assumption of its obstruction.

The complete project and external import sets are recorded below so the
inventory is reconstructible from the public import graph. This is the
statement's definition closure, not the future proof's closure. The proof
successor must audit every extra input independently.

Fresh bounded TaskHub searches for `head derivative support` and
`SegmentHeadDerivative` found no match; the broader `segment derivative`
search found other known derivative and excluded segment-socle work. These
are owner checks, not an exhaustive absence certificate.

No proof successor has been published at statement preparation. A statement's
compilation, semantic acceptance or publication does not prove it or complete
the host's full irreducibility criterion.

## Appendix: complete project import closure

- `Langlands.Group.GL.Basic`
- `Langlands.Group.GL.BlockModulus`
- `Langlands.Group.GL.Blocks`
- `Langlands.Group.GL.Mirabolic`
- `Langlands.Group.GL.MirabolicRadical`
- `Langlands.Group.GL.Nonarchimedean`
- `Langlands.Group.GL.NonarchimedeanStatement`
- `Langlands.Group.GL.NormalizedCharacter`
- `Langlands.Group.GL.Padic`
- `Langlands.Group.GL.PadicBlocks`
- `Langlands.Group.GL.RankMaps`
- `Langlands.Group.GL.UpperUnipotent`
- `Langlands.HarmonicAnalysis.Basic`
- `Langlands.LocalField.Canonical`
- `Langlands.LocalField.Definitions`
- `Langlands.LocalField.Normalization.Definitions`
- `Langlands.LocalField.Normalization.Proof`
- `Langlands.LocalField.Normalization.Statement`
- `Langlands.LocalField.Topology`
- `Langlands.Representation.Category.Basic`
- `Langlands.Representation.Category.Subquotients`
- `Langlands.Representation.Category.Twist`
- `Langlands.Representation.Classification.ConstituentRelations`
- `Langlands.Representation.Classification.SegmentHeadDerivativeSupportTruncationStatement`
- `Langlands.Representation.Classification.SegmentTruncationObstructionStatement`
- `Langlands.Representation.Classification.Segments`
- `Langlands.Representation.Classification.Supercuspidal`
- `Langlands.Representation.Classification.SupercuspidalSupport`
- `Langlands.Representation.Classification.SupercuspidalTwist`
- `Langlands.Representation.Derivative.Iteration`
- `Langlands.Representation.Derivative.MirabolicCharacter`
- `Langlands.Representation.Derivative.MirabolicMinus`
- `Langlands.Representation.Dual.Definitions`
- `Langlands.Representation.Induction.BlockFactors`
- `Langlands.Representation.Induction.Definitions`
- `Langlands.Representation.Induction.Parabolic`
- `Langlands.Representation.Jacquet.CharacterTwistEquiv`
- `Langlands.Representation.Jacquet.Coinvariants`
- `Langlands.Representation.Jacquet.Localization`
- `Langlands.Representation.Jacquet.PositiveCharacter`
- `Langlands.Representation.Jacquet.SmoothTwist`
- `Langlands.Representation.MatrixCoefficient.Definitions`
- `Langlands.Representation.MatrixCoefficient.LawsProof`
- `Langlands.Representation.MatrixCoefficient.LawsStatement`
- `Langlands.Representation.Smooth.Admissibility.CofinalProof`
- `Langlands.Representation.Smooth.Admissibility.CofinalStatement`
- `Langlands.Representation.Smooth.Admissibility.EquivalenceProof`
- `Langlands.Representation.Smooth.Admissibility.EquivalenceStatement`
- `Langlands.Representation.Smooth.Definitions`
- `Langlands.Representation.Smooth.FixedVectors.Definitions`
- `Langlands.Representation.Smooth.SmoothPart.BasicProof`
- `Langlands.Representation.Smooth.SmoothPart.BasicStatement`
- `Langlands.Representation.Smooth.SmoothPart.Definitions`
- `Langlands.Representation.Smooth.Transfer.PullbackProof`
- `Langlands.Representation.Smooth.Transfer.PullbackStatement`
- `Langlands.Representation.Smooth.Transfer.SubquotientProof`
- `Langlands.Representation.Smooth.Transfer.SubquotientStatement`
- `Langlands.Representation.Tensor.Finite`
- `Langlands.Representation.Twist.AdmissibilityProof`
- `Langlands.Representation.Twist.AdmissibilityStatement`
- `Langlands.Representation.Twist.AlgebraProof`
- `Langlands.Representation.Twist.AlgebraStatement`
- `Langlands.Representation.Twist.ContinuousCharacterProof`
- `Langlands.Representation.Twist.ContinuousCharacterStatement`
- `Langlands.Representation.Twist.Definitions`
- `Langlands.Representation.Twist.RealPower`
- `Langlands.Representation.Twist.SmoothProof`
- `Langlands.Representation.Twist.SmoothStatement`
- `Langlands.Representation.Twist.SubquotientDefinitions`
- `Langlands.Representation.Twist.SubquotientProof`
- `Langlands.Representation.Twist.SubquotientStatement`
- `Langlands.Representation.Unitary.Basic`
- `Langlands.Representation.Whittaker.Algebraic`
- `Langlands.Representation.Whittaker.GeneralLinear`
- `Langlands.Topology.CompactNormCharacter`
- `Langlands.Topology.Nonarchimedean.Subgroup`
- `Langlands.Weil.Representation.Basic`
- `Langlands.Weil.Representation.Determinant`
- `Langlands.Weil.Representation.IsomorphismInvarianceProof`
- `Langlands.Weil.Representation.Operations`

## Appendix: complete external import roots

- `Lean.Elab.Tactic.Omega`
- `Mathlib.Algebra.BigOperators.Fin`
- `Mathlib.Algebra.BigOperators.Group.Finset.Basic`
- `Mathlib.Algebra.CharP.Basic`
- `Mathlib.Algebra.Group.Hom.Instances`
- `Mathlib.Algebra.Order.Archimedean.Basic`
- `Mathlib.Algebra.Polynomial.Lifts`
- `Mathlib.Algebra.Ring.GeomSum`
- `Mathlib.Analysis.Complex.Basic`
- `Mathlib.Analysis.Complex.Circle`
- `Mathlib.Analysis.InnerProductSpace.Defs`
- `Mathlib.Analysis.Normed.Module.FiniteDimension`
- `Mathlib.Analysis.Normed.Unbundled.SpectralNorm`
- `Mathlib.Analysis.Real.Sqrt`
- `Mathlib.Analysis.SpecialFunctions.Pow.NNReal`
- `Mathlib.Analysis.SpecialFunctions.Pow.Real`
- `Mathlib.Basic.Complex.Basic`
- `Mathlib.CategoryTheory.ObjectProperty.FullSubcategory`
- `Mathlib.CategoryTheory.Pi.Basic`
- `Mathlib.CategoryTheory.Skeletal`
- `Mathlib.Data.Matrix.Block`
- `Mathlib.FieldTheory.Finite.Basic`
- `Mathlib.GroupTheory.GroupAction.ConjAct`
- `Mathlib.LinearAlgebra.Determinant`
- `Mathlib.LinearAlgebra.Dimension.Constructions`
- `Mathlib.LinearAlgebra.FiniteDimensional.Defs`
- `Mathlib.LinearAlgebra.Matrix.Block`
- `Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic`
- `Mathlib.LinearAlgebra.Matrix.Reindex`
- `Mathlib.LinearAlgebra.PiTensorProduct.Basic`
- `Mathlib.Logic.Equiv.Fin.Basic`
- `Mathlib.MeasureTheory.Integral.Bochner.Set`
- `Mathlib.MeasureTheory.Measure.Haar.Basic`
- `Mathlib.NumberTheory.Padics.LocalField`
- `Mathlib.NumberTheory.Padics.RingHoms`
- `Mathlib.Order.Atoms`
- `Mathlib.RepresentationTheory.Basic`
- `Mathlib.RepresentationTheory.Coinduced`
- `Mathlib.RepresentationTheory.Coinvariants`
- `Mathlib.RepresentationTheory.Intertwining`
- `Mathlib.RepresentationTheory.Invariants`
- `Mathlib.RepresentationTheory.Irreducible`
- `Mathlib.RepresentationTheory.Rep.Basic`
- `Mathlib.RepresentationTheory.Semisimple`
- `Mathlib.RepresentationTheory.Subrepresentation`
- `Mathlib.RingTheory.DedekindDomain.IntegralClosure`
- `Mathlib.RingTheory.FiniteLength`
- `Mathlib.RingTheory.Finiteness.Basic`
- `Mathlib.RingTheory.Noetherian.Basic`
- `Mathlib.RingTheory.Noetherian.Defs`
- `Mathlib.RingTheory.RamificationInertia.Basic`
- `Mathlib.RingTheory.Valuation.Integral`
- `Mathlib.Tactic.Linarith`
- `Mathlib.Tactic.NoncommRing`
- `Mathlib.Topology.Algebra.ContinuousMonoidHom`
- `Mathlib.Topology.Algebra.Group.Basic`
- `Mathlib.Topology.Algebra.Group.Matrix`
- `Mathlib.Topology.Algebra.Group.Units`
- `Mathlib.Topology.Algebra.Module.FiniteDimension`
- `Mathlib.Topology.Algebra.Module.ModuleTopology`
- `Mathlib.Topology.Algebra.Nonarchimedean.Basic`
- `Mathlib.Topology.Algebra.OpenSubgroup`
- `Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology`
- `Mathlib.Topology.Algebra.Valued.NormedValued`
- `Mathlib.Topology.Bases`
- `Mathlib.Topology.Compactness.Compact`
- `Mathlib.Topology.Connected.TotallyDisconnected`
- `Mathlib.Topology.Instances.NNReal.Lemmas`
- `Mathlib.Topology.LocallyConstant.Basic`
