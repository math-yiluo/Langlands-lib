# Boundary cases for highest-derivative support shift

Author: Worker 128.

This internal helper pair addresses the boundary cases of
`Langlands.Classification.HighestDerivativeSupportShift`. It does not prove the
general support-shift theorem.

At positive source rank, the general-linear derivatives of positive order jointly
detect the carrier. The proof restricts the representation to the mirabolic
subgroup, whose inclusion preserves the carrier, and applies the published
`Mirabolic.subsingleton_of_forall_mirabolicDerivative`. For each splitting
`M = n + j` of the mirabolic index, its derivative is the general-linear
derivative of order `j + 1`, after eliminating rank transports. Consequently,
an order whose derivative is nonzero and all higher derivatives vanish must
be positive. This argument uses the nonzero derivative itself and does not
require irreducibility.

A supercuspidal support at rank zero is empty: its ranks sum to zero by
`IsSupercuspidalSupport.sum_rank`, and each datum has positive rank. Mapping
the empty support by `CuspidalDatum.twist 1` gives the empty multiset, which
is below any prescribed source support. This covers both the top-derivative
case and source rank zero of the target.

The detection input is the independently accepted and published helper
`MirabolicDerivativeVanishing`, introduced in candidate
`f957ae76-3779-4436-bdcb-98bc63561e07`, reviewed by Reviewer 4988 and published
at commit `2b8beb8bd3034a40aeb5dc7b2de17b607fae8d11`. Its source rationale is
BZ77 §3.5, printed p.452. The present restriction and rank-transport argument
is internal. The support calculation follows directly from the published
support definition; no support existence or uniqueness theorem is assumed.

The topology is the supplied `T.topology`; the field and carrier universes
remain independent for detection. Support calculations use the required
carrier universe `max uF uV`. All derivatives are the existing
determinant inverse-half normalized functors. This proof uses their carriers
and rank-index definitions only, so no Haar-modulus comparison is needed.

## Declarations and boundary scope

The internal predicate
`Langlands.Derivative.PositiveGeneralLinearDerivativesVanish T ψ A`
means that every actual order-`j` derivative, `0 < j ≤ N`, of `A : GL_N`
has a subsingleton carrier. It abbreviates a vanishing condition and asserts
no detection theorem. It retains the supplied topology, the actual derivative
functors and an arbitrary carrier universe `uV`.

The four proved declarations are:

- `Langlands.Derivative.subsingleton_of_forall_generalLinearDerivative`: for
  `0 < N`, if `PositiveGeneralLinearDerivativesVanish T ψ A` holds, then
  the carrier of the smooth representation of `GL_N` is subsingleton.
  Its carrier universe is arbitrary `uV`.
- `Langlands.Derivative.highestGeneralLinearDerivativeOrder_pos`: for
  `0 < N` and `k ≤ N`, a nontrivial order-`k` derivative together with
  vanishing of all bounded higher derivatives implies `0 < k`. If `k = 0`,
  the order-zero functor is the identity; nontriviality of that derivative
  contradicts the preceding detection result. There is no irreducibility
  hypothesis.
- `Langlands.PadicField.TopologicalData.IsSupercuspidalSupport.eq_zero_of_rank_zero`:
  a supplied actual support `s` of a representation of `GL_n`, with `n = 0`,
  is the empty multiset. Multiset induction uses `sum_rank` and the positive
  rank of each cuspidal datum.
- `Langlands.PadicField.TopologicalData.IsSupercuspidalSupport.twist_le_of_rank_zero`:
  for that support and any multiset `s`, the positive-twist inequality
  `s'.map (CuspidalDatum.twist 1) ≤ s` follows by rewriting `s' = 0` and using
  the multiset order's least element.

For the full target, derivative rank `N-k = 0` covers `k = N`, including
`N = 0`. At positive source rank the second lemma rules out `k = 0`.
No result about the remaining orders `0 < k < N` is asserted here. The
rank-transport proof obtains `N = M+1`, restricts to `P_(M+1)`, and handles
all splittings `M = n+j`. It proves equality of the residual natural-number
ranks by `omega`, substitutes that equality, and then uses the given
order-`(j+1)` vanishing. It does not choose a level witness or identify field
and carrier universes.

## Original sources and internal provenance

The registered BZ77 original is *Induced representations of reductive p-adic
groups I*, literature ID `bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
Proposition 3.2(e), printed p.451 (one-based PDF page 12), gives the exact
sequence underlying one-step detection; §3.5, printed p.452 (PDF page 13),
iterates it to detect a mirabolic representation by its derivatives. The
present proof uses the independently proved vanishing consequence and rank
induction described below; it does not assume that exact sequence.
The restriction from `GL_N` and the explicit rank transports are internal
consequences of the existing definitions.

The support definition comes from Zelevinsky, *Induced representations of
reductive p-adic groups II*, §1.10, printed p.174 (PDF page 11), literature
ID `zelevinsky-1980-induced-ii`, SHA256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
Its cuspidal classes have positive ranks. Empty support at total rank zero
is internal multiset arithmetic on the Library definition, and is not
claimed as a separate theorem printed there. The positive twist in the
helper is literally `CuspidalDatum.twist 1`, as in the parent target. The
rank-zero argument works by empty support and therefore requires no
calculation of a nonempty twisted support.

The original BZ77 §3.5 and parent proof passages, Ze80 §1.10 and the rendered
Ze80 4.4(d) were read for this task. The lower detection source was also
read in the earlier detection audit. The project source
and errata pointers contained no applicable correction; this records the
bounded check, not an assertion that no possible erratum exists.

## Mathematical dependencies and publication provenance

Only the following mathematical steps enter the four proofs: the existing
restriction, derivative and rank-cast definitions; mirabolic joint
vanishing detection; the identity order-zero derivative; the rank-sum
field of an actual support; positive datum ranks; and elementary natural
number and multiset reasoning. No existence, uniqueness or permutation
statement about supports is assumed.

| Published helper | Accepted publication and review | Actual mathematical use |
| --- | --- | --- |
| `MirabolicDerivativeVanishing` | `f957ae76-3779-4436-bdcb-98bc63561e07`, Workers 1024 and 805, Reviewer 4988; commit `2b8beb8bd3034a40aeb5dc7b2de17b607fae8d11` | The directly used `subsingleton_of_forall_mirabolicDerivative` proves joint detection by rank induction. At rank zero the radical is trivial, so the trivial-character relation span is zero and equality in the quotient is equality of vectors. At positive rank apply the next row. The other three pairing-related modules of this publication are not imported. |
| `MinusVanishing` | `c6026915-8731-45a8-bd21-ef1ac39654b8`, Worker 1025, Reviewer 4480; commit `771cfc69d1ff795522e29cdead1b7c40f1a1c308` | `subsingleton_of_psiMinus_phiMinus` is a proved, independently reviewed helper included in a `lean.definition` publication. It converts vanished quotients into full relation spaces, transports nonzero radical characters by Levi conjugation, and uses character averages and finite Fourier orthogonality to kill each vector. It is not a statement assumed as a proof. |
| `MirabolicLatticeBox` | Inherited lower helper reviewed in `2279aa64-eb04-4afa-89a9-1ea9ac87cbe2`, Reviewer 3969; commit `b0ef093b63d0f0c27bb690dca12820c991756955` | Compact open radical-coordinate boxes, dual boxes and finite character sums used by `MinusVanishing`. The larger submission's product irreducibility theorem is not imported or used. |
| `Jacquet.CharacterAveraging` | `faa65dca-289a-4fb5-941a-b5e1200ff62e`, Reviewer 4000; commit `cb6a47b2390bdcd0be78fac0552b7fd5c46cd51b` | Finite orbit means and finite relation-span induction yield eventual zero twisted averages. The current code extracts the identical orbit-translation argument to `Compact.OrbitMeanTranslation`. No deformation/product conclusion is used. |
| `PadicAdditiveConductorProof` and the scalar annihilator helper in `ZeroRowLastRowCutoffProof` | Respectively `8f35e474-ea64-4213-b49c-80f70e559886`, Reviewer 2908, commit `6543e70ef8c82ed8535a0f9fd06c59ed896bc738`; and `c1ca32b0-5a13-4540-95ca-4b21576ff387`, Reviewer 3434, commit `6d91111e6f9b7a27124b1de32a4984bbdd222a61` | Actual valuation-lattice/conductor arithmetic and annihilators. The cutoff module's two topology proofs have been extracted unchanged to `PadicLatticeTopology`. No Whittaker finiteness or Rankin–Selberg classification result is used. |
| `SupercuspidalSupport.sum_rank` and `CuspidalDatum.rank_pos` | Existing published `SupercuspidalSupport` and `Segments` constructions | `sum_rank` extracts the equality of the sum of the given ordered factor ranks with the ambient rank; `rank_pos` is a structure field. The support calculation does not use the other theorems or segment constructions in these modules. |

The current `MirabolicDerivativeVanishing` and `MinusVanishing` pairs were
compared byte for byte with both their frozen accepted files and their
publication commits; they agree. The lower proof/source and independent
review audit of the averaging, conductor, lattice and annihilator helpers
was performed in Worker 128's earlier one-step detection task
`2871b0c7-cd63-4910-99a3-db5638fa30d1`. Those proof files remain byte-identical
at the present base, including the recorded extractions. The added
`NormalizedCharacter.determinantNorm_eq_one_of_mem_compact` theorem imports
`Topology.CompactNormCharacter`, an elementary proof that a continuous
positive character is trivial on a compact subgroup: compactness bounds its
powers and inverse powers. This addition has no excluded dependency and is
not used by the present carrier argument.

The support branch imports `Segments` for the datum and twist definitions.
That module's head/socle relations and transport lemmas express actual maps
and equivalences; none supplies a head/socle existence, formula or
classification theorem. They are not used in the four proofs. The other
support-branch imports construct normalized induction, twists,
subquotients and elementary representation equivalences. The larger
Rankin–Selberg/Whittaker import branch supplies lattice topology, character
or quotient constructions. Its algebraic Whittaker definitions do not
supply a model, multiplicity-one result or finiteness conclusion. No
finite-length, admissibility or finite-dimensionality hypothesis is added
to detection.

## Import audit

The only direct imports are
`Langlands.Representation.Classification.SupercuspidalSupport` and
`Langlands.Representation.Derivative.MirabolicDerivativeVanishing`.
Their recursively followed project closure has exactly 101 published
modules, listed below. All 202 Lean/Markdown files agree byte for byte
with the workspace's immutable Library base
`26e9adf301abba95f343f5005d9f478af9fc09d4`. The entire existing base's
13,045 Lean/Markdown files were also checked unchanged before adding this
new pair. In particular the target pair and all its imports are untouched.
No import of the parent six-statement module is needed for these helpers.

```text
Langlands.Analysis.Local.QuotientMeasure
Langlands.Group.GL.Basic
Langlands.Group.GL.BlockModulus
Langlands.Group.GL.Blocks
Langlands.Group.GL.Mirabolic
Langlands.Group.GL.MirabolicRadical
Langlands.Group.GL.Nonarchimedean
Langlands.Group.GL.NonarchimedeanStatement
Langlands.Group.GL.NormalizedCharacter
Langlands.Group.GL.Padic
Langlands.Group.GL.PadicBlocks
Langlands.Group.GL.RankMaps
Langlands.Group.GL.UpperUnipotent
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
Langlands.Representation.Category.Subquotients
Langlands.Representation.Category.Twist
Langlands.Representation.Classification.ConstituentRelations
Langlands.Representation.Classification.Segments
Langlands.Representation.Classification.Supercuspidal
Langlands.Representation.Classification.SupercuspidalSupport
Langlands.Representation.Classification.SupercuspidalTwist
Langlands.Representation.Compact.Definitions
Langlands.Representation.Compact.FiniteMean
Langlands.Representation.Compact.OrbitMeanTranslation
Langlands.Representation.Compact.ProjectionProof
Langlands.Representation.Compact.ProjectionStatement
Langlands.Representation.Derivative.Homogeneity
Langlands.Representation.Derivative.Iteration
Langlands.Representation.Derivative.MinusVanishing
Langlands.Representation.Derivative.MirabolicCharacter
Langlands.Representation.Derivative.MirabolicDerivativeDetectionStatement
Langlands.Representation.Derivative.MirabolicDerivativeVanishing
Langlands.Representation.Derivative.MirabolicLatticeBox
Langlands.Representation.Derivative.MirabolicMinus
Langlands.Representation.Dual.Definitions
Langlands.Representation.Induction.BlockFactors
Langlands.Representation.Induction.Definitions
Langlands.Representation.Induction.Parabolic
Langlands.Representation.Jacquet.CharacterAveraging
Langlands.Representation.Jacquet.CharacterTwistEquiv
Langlands.Representation.Jacquet.Coinvariants
Langlands.Representation.Jacquet.Localization
Langlands.Representation.Jacquet.PositiveCharacter
Langlands.Representation.Jacquet.SmoothTwist
Langlands.Representation.MatrixCoefficient.Definitions
Langlands.Representation.MatrixCoefficient.LawsProof
Langlands.Representation.MatrixCoefficient.LawsStatement
Langlands.Representation.RankinSelberg.LastRowCompactOrbitProof
Langlands.Representation.RankinSelberg.LastRowCompactOrbitStatement
Langlands.Representation.RankinSelberg.QuotientIntegrals
Langlands.Representation.RankinSelberg.ZeroRowLastRowCutoffProof
Langlands.Representation.RankinSelberg.ZeroRowLastRowCutoffStatement
Langlands.Representation.Smooth.Admissibility.CofinalProof
Langlands.Representation.Smooth.Admissibility.CofinalStatement
Langlands.Representation.Smooth.Admissibility.EquivalenceProof
Langlands.Representation.Smooth.Admissibility.EquivalenceStatement
Langlands.Representation.Smooth.Definitions
Langlands.Representation.Smooth.FixedVectors.Definitions
Langlands.Representation.Smooth.SmoothPart.BasicProof
Langlands.Representation.Smooth.SmoothPart.BasicStatement
Langlands.Representation.Smooth.SmoothPart.Definitions
Langlands.Representation.Smooth.Transfer.PullbackProof
Langlands.Representation.Smooth.Transfer.PullbackStatement
Langlands.Representation.Smooth.Transfer.SubquotientProof
Langlands.Representation.Smooth.Transfer.SubquotientStatement
Langlands.Representation.Tensor.Finite
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
Langlands.Topology.Nonarchimedean.Subgroup
Langlands.Weil.Representation.Basic
Langlands.Weil.Representation.Determinant
Langlands.Weil.Representation.IsomorphismInvarianceProof
Langlands.Weil.Representation.Operations
```

## Condition-by-condition exclusion audit

The audit follows both the entire import closure and the actual proof
chain above. A scan of the 101 Lean files and their Markdown companions
against all 54 explicit forbidden declaration/task identifiers in the
contract found no Lean hits. The six matching Markdown lines are
independence disclaimers in `Iteration`, `MirabolicMinus` and
`MirabolicDerivativeVanishing`. The mathematical inspection is also
necessary: an identifier scan alone cannot exclude a renamed result.
The following table records every listed exclusion, including repeated
upstream restrictions, as absent from the mathematical proof chain and
from imported proof dependencies. Task IDs identify prohibitions only.

| Excluded conclusion or task family | Audit result |
| --- | --- |
| `UnlinkedSegmentSocleProductIrreducible`, `LinkedSegmentSocleReverseProductStructure`, `LinkedSegmentSoclePairReducible`; `23e98d90-6055-4e35-91a9-b0f5d8a84961`, `a55c4267-7e3a-43f6-8bb1-ce319e1d0aa9`, `8fa9f68b-fa1b-431a-97f6-5b163964d1fc` | No such module, conclusion or successor enters the closure or proof. Joint detection precedes segment products. |
| `JuxtaposedSegmentSocleReverseProductStructure`, `LinkedSegmentSocleReverseProductQuotientHom`; `7ff2a1e9-89dc-439e-a861-a567b3db92bf` and successors | No linked or juxtaposed pair structure or quotient result is used. |
| `SegmentSocleProductIrreducibility`; `2ae5cbe5-0701-4509-88a0-db8cbeb35be4` | No socle product criterion is imported or applied. |
| `AdjacentUnlinkedSegmentSocleSwap`; `e3634665-571b-4852-9f4c-bab8a1053434`, `cded83f3-df9c-4018-bc61-dc54f5c1f9ab` | No adjacent commutation or swap result is used. |
| `TwoSegmentSocleCommutation`; `426911b4-6620-413f-8065-04b25287f3bd`, `66e3b87c-647e-41e4-af18-df4d436765f0` | No two-segment commutation result is used. |
| `LinkedSegmentSocleGluing`; `c84cd52c-3ff3-4024-be50-8b84dd480888`, `6780b79c-9526-46aa-b8b4-00377d68b1ea` | No gluing result is used. |
| `OrderedMultisegmentSocleExistence`; `23189526-80b0-4828-a6d4-7ebec2cbeef5` | The proof uses no ordered socle construction or existence. |
| `MultisegmentSocleExhaustion`; `f3a69bc8-7312-4f82-8a7d-ea3c8188cb63` | No multisegment exhaustion is used. |
| Analytic segment classification; `aca8805b-054f-4d56-8045-12db7f623404` | The proof uses only actual relation quotients and elementary support arithmetic. |
| Special-head multisegment exhaustion; `3bfb61fa-1129-4fc9-83fd-7fcfec22106e` | No special-head exhaustion is used. |
| Ordered special/strong-head existence; `ebea9a8a-9b21-4208-aa31-98c2dea1f8a3` | No ordered head existence is used. |
| Quotient coverage; `20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584` | No quotient coverage theorem is used. |
| Ordered conversion; `8252833d-c269-41a9-824c-5879e531b23b` | No multisegment conversion theorem is used. |
| Tempered block uniqueness; `52e97845-36bb-457d-b76f-70753334b88c` | No tempered or block uniqueness theorem is used. |
| `GenericSegmentProductUniqueness`; `30341ae4-65f2-4a0e-9283-763db01a409e` | No generic segment uniqueness result is used. |
| `SquareIntegrableLanglandsClassification`; `1cb45da2-7007-4351-a694-594fb148b8d1` | No square-integrable classification is used. |
| Square-integrable exhaustion; `cd8ab97c-0b78-4bce-97c4-d307a28159a4` | No square-integrable exhaustion is used. |
| Regular exhaustion; `bf433f0a-921a-428c-b0c0-6475438125ac` | No regular exhaustion is used. |
| `SegmentSpecialEssentialSquareIntegrability`, forward special-segment essential square-integrability; `5eece9e8-7f6b-4ea9-abea-a1f9f1b8c807` | No forward or special square-integrability result is used. |
| `SegmentHeadProductIrreducibility`; `8364e73f-14ec-4d14-8f2b-1555a7c1ce95` | No special-head criterion or its consequences are used. |
| Individual special-head/reverse-socle existence; `67279e36-f3c2-42e3-9302-11729784042e` | `Segments` supplies relations only; no individual existence assertion is used. |
| Individual segment-socle/reverse-head existence; `4ca79bbd-589e-476b-9f65-661e799984b5` | No individual socle/head existence assertion is used. |
| `SegmentFullJacquetFormula`; `ed48ae06-964c-4c84-9e62-978f5a953ca7` and exact proof successor | No full segment Jacquet formula is used. The relation-space and averaging constructions are general lower algebra. |
| `SegmentHeadJacquetFormula`; `55ad1e10-62d8-46b7-a081-909ef0056426` | No head Jacquet formula is used. |
| `SegmentSocleJacquetFormula`; `b95105c6-f8bb-4641-ae53-2f49d1e7f034` | No socle Jacquet formula is used. |
| `SegmentSpecialJacquetExponentNormFormula`; `92aea10f-62ac-4e0b-bd4a-9a80909797c5` | No segment exponent-norm formula is used. |
| `TwoSupercuspidalNonadjacentProductIrreducible`; `3c9849a4-a6c0-43ac-9982-d15ed76bf1e9` | No nonadjacent two-supercuspidal irreducibility result is used. |
| `TwoSupercuspidalProductStructure`; `ab61f565-1427-4746-ba77-46097563e962` | No full product structure, adjacent composition or Jacquet conclusion is used. |
| Every segment derivative formula, including Ze80 §§3.5, 9.6 and parent clauses (b), (d), (e), (f) | No segment derivative statement or proof module is imported. The derivative input is general mirabolic joint vanishing, with its actual proof and independent publication checked. |
| Every segment-socle/head existence or Jacquet formula, and segment classification | The only imported segment layer defines the cuspidal datum, twists, segments and constituent relations. The four proofs use datum ranks, twists of the empty multiset, and support rank sums. |
| Ze80 product criteria 4.2, 9.7, analytic/square-integrability result 9.3, classification and exhaustion theorems | None supplies any step. In particular the linked-pair converse is not used circularly for Proposition 1.11. |
| Unproved derivative statements, citations, conditional assemblies or pending tasks | The used mirabolic detection lemmas are fully proved and independently accepted/published. Neither minus exactness, general-linear exactness, Leibniz filtration, mixed products, pairing, nor parent clause (a) is needed here. |

All rows exclude mathematical conclusions, proof successors and transitive
dependents, including renamed versions. No new prerequisite task is
introduced. The complete parent theorem, its nonboundary orders and its
required notifications remain obligations of task
`f81d9b36-2615-4fec-abc2-50ef93d880bf`; acceptance of this helper does not
complete that task.
