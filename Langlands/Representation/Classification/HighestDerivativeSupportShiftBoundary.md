# Boundary cases for highest-derivative support shift

This internal helper file addresses the boundary cases of
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

The detection input is the proved helper
`MirabolicDerivativeVanishing`, added to the Library at commit
`2b8beb8bd3034a40aeb5dc7b2de17b607fae8d11`. Its source rationale is
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
Ze80 4.4(d) were read for this file. The lower detection source was also
read for the audit recorded on the page of
`Derivative.MirabolicOneStepDetectionProof`. The project source
and errata pointers contained no applicable correction; this records the
bounded check, not an assertion that no possible erratum exists.

## Mathematical dependencies and publication provenance

Only the following mathematical steps enter the four proofs: the existing
restriction, derivative and rank-cast definitions; mirabolic joint
vanishing detection; the identity order-zero derivative; the rank-sum
field of an actual support; positive datum ranks; and elementary natural
number and multiset reasoning. No existence, uniqueness or permutation
statement about supports is assumed.

| Published helper | Added to the Library at | Actual mathematical use |
| --- | --- | --- |
| `MirabolicDerivativeVanishing` | commit `2b8beb8bd3034a40aeb5dc7b2de17b607fae8d11` | The directly used `subsingleton_of_forall_mirabolicDerivative` proves joint detection by rank induction. At rank zero the radical is trivial, so the trivial-character relation span is zero and equality in the quotient is equality of vectors. At positive rank apply the next row. The other three pairing-related modules of this publication are not imported. |
| `MinusVanishing` | commit `771cfc69d1ff795522e29cdead1b7c40f1a1c308` | `subsingleton_of_psiMinus_phiMinus` is a proved helper theorem of this module. It converts vanished quotients into full relation spaces, transports nonzero radical characters by Levi conjugation, and uses character averages and finite Fourier orthogonality to kill each vector. It is not a statement assumed as a proof. |
| `MirabolicLatticeBox` | commit `b0ef093b63d0f0c27bb690dca12820c991756955` (a lower helper) | Compact open radical-coordinate boxes, dual boxes and finite character sums used by `MinusVanishing`. The product irreducibility theorem added to the Library together with it is not imported or used. |
| `Jacquet.CharacterAveraging` | commit `cb6a47b2390bdcd0be78fac0552b7fd5c46cd51b` | Finite orbit means and finite relation-span induction yield eventual zero twisted averages. The Library code extracts the identical orbit-translation argument to `Compact.OrbitMeanTranslation`. No deformation/product conclusion is used. |
| `PadicAdditiveConductorProof` and the scalar annihilator helper in `ZeroRowLastRowCutoffProof` | Respectively commit `6543e70ef8c82ed8535a0f9fd06c59ed896bc738` and commit `6d91111e6f9b7a27124b1de32a4984bbdd222a61` | Actual valuation-lattice/conductor arithmetic and annihilators. The cutoff module's two topology proofs have been extracted unchanged to `PadicLatticeTopology`. No Whittaker finiteness or Rankin–Selberg classification result is used. |
| `SupercuspidalSupport.sum_rank` and `CuspidalDatum.rank_pos` | Existing published `SupercuspidalSupport` and `Segments` constructions | `sum_rank` extracts the equality of the sum of the given ordered factor ranks with the ambient rank; `rank_pos` is a structure field. The support calculation does not use the other theorems or segment constructions in these modules. |

The `MirabolicDerivativeVanishing` and `MinusVanishing` pairs used here were
compared byte for byte with their files at the commits above; they agreed.
The proof and source audit of the averaging, conductor, lattice and
annihilator helpers is recorded on the page of
`Derivative.MirabolicOneStepDetectionProof`. Those proof files were
byte-identical at the Library base of the import audit below, including the
recorded extractions. The added
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
with the Library base
`26e9adf301abba95f343f5005d9f478af9fc09d4`. The entire existing base's
13,045 Lean/Markdown files were also checked unchanged before adding this
new pair. In particular the target pair and all its imports are untouched.
No import of the parent six-statement module
`Classification.SegmentSocleDerivativesStatement` is needed for these helpers.

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
against all 54 explicit excluded identifiers found no Lean hits. The six matching Markdown lines are
independence disclaimers in `Iteration`, `MirabolicMinus` and
`MirabolicDerivativeVanishing`. The mathematical inspection is also
necessary: an identifier scan alone cannot exclude a renamed result.
The following table records every listed exclusion, including repeated
upstream restrictions, as absent from the mathematical proof chain and
from imported proof dependencies.

| Excluded conclusion | Audit result |
| --- | --- |
| `UnlinkedSegmentSocleProductIrreducible`, `LinkedSegmentSocleReverseProductStructure`, `LinkedSegmentSoclePairReducible` | No such module, conclusion or proof of one enters the closure or proof. Joint detection precedes segment products. |
| `JuxtaposedSegmentSocleReverseProductStructure`, `LinkedSegmentSocleReverseProductQuotientHom` and their proofs | No linked or juxtaposed pair structure or quotient result is used. |
| `SegmentSocleProductIrreducibility` | No socle product criterion is imported or applied. |
| `AdjacentUnlinkedSegmentSocleSwap` | No adjacent commutation or swap result is used. |
| `TwoSegmentSocleCommutation` | No two-segment commutation result is used. |
| `LinkedSegmentSocleGluing` | No gluing result is used. |
| `OrderedMultisegmentSocleExistence` | The proof uses no ordered socle construction or existence. |
| `MultisegmentSocleExhaustion` | No multisegment exhaustion is used. |
| Analytic segment classification | The proof uses only actual relation quotients and elementary support arithmetic. |
| Special-head multisegment exhaustion | No special-head exhaustion is used. |
| Ordered special/strong-head existence | No ordered head existence is used. |
| Quotient coverage | No quotient coverage theorem is used. |
| Ordered conversion | No multisegment conversion theorem is used. |
| Tempered block uniqueness | No tempered or block uniqueness theorem is used. |
| `GenericSegmentProductUniqueness` | No generic segment uniqueness result is used. |
| `SquareIntegrableLanglandsClassification` | No square-integrable classification is used. |
| Square-integrable exhaustion | No square-integrable exhaustion is used. |
| Regular exhaustion | No regular exhaustion is used. |
| `SegmentSpecialEssentialSquareIntegrability`, forward special-segment essential square-integrability | No forward or special square-integrability result is used. |
| `SegmentHeadProductIrreducibility` | No special-head criterion or its consequences are used. |
| Individual special-head/reverse-socle existence | `Segments` supplies relations only; no individual existence assertion is used. |
| Individual segment-socle/reverse-head existence | No individual socle/head existence assertion is used. |
| `SegmentFullJacquetFormula` and its proof | No full segment Jacquet formula is used. The relation-space and averaging constructions are general lower algebra. |
| `SegmentHeadJacquetFormula` | No head Jacquet formula is used. |
| `SegmentSocleJacquetFormula` | No socle Jacquet formula is used. |
| `SegmentSpecialJacquetExponentNormFormula` | No segment exponent-norm formula is used. |
| `TwoSupercuspidalNonadjacentProductIrreducible` | No nonadjacent two-supercuspidal irreducibility result is used. |
| `TwoSupercuspidalProductStructure` | No full product structure, adjacent composition or Jacquet conclusion is used. |
| Every segment derivative formula, including Ze80 §§3.5, 9.6 and parent clauses (b), (d), (e), (f) | No segment derivative statement or proof module is imported. The derivative input is general mirabolic joint vanishing, with its actual proof and publication checked. |
| Every segment-socle/head existence or Jacquet formula, and segment classification | The only imported segment layer defines the cuspidal datum, twists, segments and constituent relations. The four proofs use datum ranks, twists of the empty multiset, and support rank sums. |
| Ze80 product criteria 4.2, 9.7, analytic/square-integrability result 9.3, classification and exhaustion theorems | None supplies any step. In particular the linked-pair converse is not used circularly for Proposition 1.11. |
| Unproved derivative statements, citations or conditional assemblies | The used mirabolic detection lemmas are fully proved. Neither minus exactness, general-linear exactness, Leibniz filtration, mixed products, pairing, nor parent clause (a) is needed here. |

All rows exclude mathematical conclusions, the files proving them and transitive
dependents, including renamed versions. The complete parent theorem and
its nonboundary orders are not proved here; the Library proves
`HighestDerivativeSupportShift` as `highestDerivativeSupportShift` in
`HighestDerivativeSupportShiftProof`.
