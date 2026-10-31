# Proof of the rank-one boundary of mirabolic derivative detection

Author: Worker 1132. No draft by another worker was reused.

The theorem `Langlands.Derivative.mirabolicRankOneDetection` proves exactly the
published proposition `Langlands.Derivative.MirabolicRankOneDetection.{uF,uV} F T`
from `Langlands.Representation.Derivative.MirabolicRankOneDetectionStatement`.
Its outer telescope is
`{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)`, and its
type is `MirabolicRankOneDetection.{uF, uV} F T` with the two universe parameters
`uF` and `uV` kept independent. The statement pair and every module it imports are
used unchanged.

## Exact scope

After installing the supplied `T.topology`, the proposition says: for every actual
smooth complex representation `A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear.mirabolic 0 F.Carrier)`,

```lean
Subsingleton ((Mirabolic.psiMinus T 0).obj A) → Subsingleton A
```

The Library's `mirabolic 0` is BZ77's `P_1`, and `Mirabolic.psiMinus T 0` is the
actual normalized `Ψ⁻` to `GL_0`. Both `Subsingleton` predicates concern the actual
underlying vector spaces. The proof covers every smooth source representation,
including infinite-dimensional, infinite-length and nonadmissible ones. It adds no
premise. In particular it uses no additive character, finite length, admissibility,
irreducibility or Haar-modulus comparison. It introduces no new quotient, no
parallel `Ψ⁻`, no `P_0` and no order-zero derivative.

## Implemented Lean proof

The module adds two helper theorems in namespace `Langlands.Derivative.Mirabolic`
and then the target theorem.

1. **`relations_rankOne_eq_bot T`.** For every `A` as above,
   `Jacquet.Localization.relations A.representation (radical 0 F.Carrier) 1 = ⊥`.
   The proof unfolds `relations` as the span of the vectors
   `ρ(u)v - (θ u : ℂ) • v`, here with `θ = 1`, and reduces `⊥`-containment of the
   span to its generators (`eq_bot_iff`, `Submodule.span_le`). For a generator
   indexed by `(u, v)`, the published instance
   `GeneralLinear.Mirabolic.radical_rankOneSubsingleton : Subsingleton (radical 0 F)`
   gives `u = 1` (applied explicitly through `Subsingleton.elim`). Then
   `simp only` closes the goal: `ρ(1)` is the identity map (`map_one`,
   `Module.End.one_apply`), the trivial character value is `1`
   (`Units.val_one`, `one_smul`), and `v - v = 0` (`sub_self`) lies in `⊥`.

2. **`psiMinusQuotient_rankOne_injective T`.** For every `A`, the actual quotient
   map `Mirabolic.psiMinusQuotient T 0 A` is injective. By
   `LinearMap.ker_eq_bot`, it suffices that its kernel is `⊥`. The published
   theorem `Mirabolic.ker_psiMinusQuotient T 0 A` identifies this kernel with
   the relation submodule above, so step 1 finishes the proof.

3. **`mirabolicRankOneDetection F T`.** Given `A` and
   `hA : Subsingleton ((Mirabolic.psiMinus T 0).obj A)`, the proof reads `hA` as
   `Subsingleton (Jacquet.Localization.Coinvariants A.representation (radical 0 F.Carrier) 1)`.
   This is a definitional equality. It is the content of the published `rfl` lemma
   `Mirabolic.psiMinus_obj_carrier`: the normalized functor is the unnormalized
   localization followed by the determinant inverse-half twist, and the twist changes
   the action but not the carrier. An injective map into a subsingleton type has a
   subsingleton domain (`Function.Injective.subsingleton`). Applied to the injective
   map of step 2, this gives `Subsingleton A`.

Development check `8b139347-6eac-4984-b5a4-0c5d6a573366`, in approved environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` over Library commit
`4c0ab0f3966f1a1836901963afb04dca21607ffb`, compiled this module with zero errors
and zero warnings. Its inspection of the final theorem reports level parameters
`uF`, `uV` and only the axioms `propext`, `Classical.choice` and `Quot.sound`.
Compilation is not independent acceptance or publication.

## Published inputs

Each input is a published Library result, used unchanged by its Lean name:

- `GeneralLinear.Mirabolic.radical_rankOneSubsingleton` (instance,
  `Langlands.Group.GL.MirabolicRadical`). It is declared by `inferInstance` for a
  subgroup of the rank-one mirabolic group. That group is a subsingleton by
  `GeneralLinear.Mirabolic.rankOneSubsingleton`, which is built from
  `GeneralLinear.Mirabolic.rankOne_eq_one` (`Langlands.Group.GL.Mirabolic`).
- `Langlands.Derivative.Mirabolic.psiMinusQuotient`,
  `Langlands.Derivative.Mirabolic.ker_psiMinusQuotient`,
  `Langlands.Derivative.Mirabolic.psiMinus` and the definitional fact recorded by
  `Langlands.Derivative.Mirabolic.psiMinus_obj_carrier`
  (`Langlands.Representation.Derivative.MirabolicMinus`).
- `Jacquet.Localization.relations` and `Jacquet.Localization.Coinvariants`
  (`Langlands.Representation.Jacquet.Localization`).
- The Mathlib lemmas named above.

The Library module `Langlands.Representation.Derivative.MirabolicDerivativeVanishing`
contains a related rank-zero lemma, `subsingleton_of_psiMinus_zero`. This proof neither
imports nor uses that module, nor any all-order or positive-rank detection result.

## Relation to the source

The registered original is Bernstein–Zelevinsky, *Induced representations of
reductive p-adic groups I* (1977), source `bernstein-zelevinsky-1977-induced-i`,
SHA256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
Section 3.2, printed p.451 (one-based PDF page 12), gives the exactness of the
functors and the sequence `0 → Φ⁺Φ⁻ → Id → Ψ⁺Ψ⁻ → 0`. Section 3.5, printed p.452
(PDF page 13), defines `τ^(k) = Ψ⁻(Φ⁻)^(k-1)(τ)` for `τ ∈ Alg P_n`. It then glues
`τ` from a natural filtration whose quotients are `(Φ⁺)^(k-1)Ψ⁺(τ^(k))`. The
last step of `τ^(n)` applies `Ψ⁻` to a representation of `P_1`.

The source states no separate rank-one detection lemma. The present theorem is an
internal elementary boundary assertion. The implemented proof does not follow the
source's filtration argument: it constructs no filtration and uses no `Φ⁺`, `Ψ⁺`,
exactness, adjunction or the sequence of section 3.2. It uses only the triviality
of the rank-one radical and the explicit kernel of the actual quotient map. No
applicable erratum is recorded in the project literature records for this source.
The proof does not depend on any source passage.

## Import closure audit

The module's sole import is
`Langlands.Representation.Derivative.MirabolicRankOneDetectionStatement`. Its
complete transitive project import closure was computed by following every
`import Langlands.*` line recursively. It was compared with Library commit
`4c0ab0f3966f1a1836901963afb04dca21607ffb`, the workspace base. The closure has 51
project modules: the statement module, `MirabolicMinus`, and 49 further
dependencies. Each module's Lean file and paired Markdown file are byte-identical
(SHA256) to the published files at that commit. None of these Lean files, nor this
proof module, contains `sorry`, `admit`, an `axiom` declaration, `unsafe`,
`extern` or `implemented_by`. Standard Mathlib modules are outside this list.

```text
Langlands.Group.GL.Basic
Langlands.Group.GL.Mirabolic
Langlands.Group.GL.MirabolicRadical
Langlands.Group.GL.Nonarchimedean
Langlands.Group.GL.NonarchimedeanStatement
Langlands.Group.GL.NormalizedCharacter
Langlands.Group.GL.Padic
Langlands.Group.GL.RankMaps
Langlands.Group.GL.UpperUnipotent
Langlands.HarmonicAnalysis.Basic
Langlands.LocalField.Canonical
Langlands.LocalField.Definitions
Langlands.LocalField.Normalization.Definitions
Langlands.LocalField.Normalization.Proof
Langlands.LocalField.Normalization.Statement
Langlands.LocalField.Topology
Langlands.Representation.Category.Basic
Langlands.Representation.Category.Twist
Langlands.Representation.Derivative.MirabolicCharacter
Langlands.Representation.Derivative.MirabolicMinus
Langlands.Representation.Derivative.MirabolicRankOneDetectionStatement
Langlands.Representation.Dual.Definitions
Langlands.Representation.Jacquet.Coinvariants
Langlands.Representation.Jacquet.Localization
Langlands.Representation.Jacquet.SmoothTwist
Langlands.Representation.MatrixCoefficient.Definitions
Langlands.Representation.MatrixCoefficient.LawsProof
Langlands.Representation.MatrixCoefficient.LawsStatement
Langlands.Representation.Smooth.Admissibility.CofinalProof
Langlands.Representation.Smooth.Admissibility.CofinalStatement
Langlands.Representation.Smooth.Definitions
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
Langlands.Representation.Whittaker.Algebraic
Langlands.Representation.Whittaker.GeneralLinear
Langlands.Topology.Nonarchimedean.Subgroup
```

The closure consists of local-field and matrix-group constructions, smooth
representation and category foundations, character twists, actual localized
coinvariants and their functoriality, and the mirabolic character and minus
functors. Its `Whittaker` modules supply the standard character and algebraic
Whittaker constructions with elementary lemmas. They contain no Whittaker-model
existence, uniqueness or classification result. The closure contains no segment,
multisegment, parabolic-product, head, socle, classification, square-integrability,
plus-functor or exactness module. It does not contain
`MirabolicDerivativeVanishing`, `MirabolicDerivativeDetectionProof` or any
positive-rank one-step detection module.

## Mathematical dependency and exclusion audit

The proof uses only the inputs listed above. Its mathematical content is that
the rank-one radical is trivial and the actual quotient map has the stated kernel.
It assumes no derivative result: neither the all-order detection statement
`Langlands.Derivative.MirabolicDerivativeDetection`, nor the positive-rank one-step
statement of task `77ea7de9-a4f6-4ed4-a532-d7dbf0180707`, nor any other pending
derivative theorem. It uses no Ze80 material, including the segment derivative
formulas of Ze80 sections 3.5 and 9.6, the segment product irreducibility criteria
(Ze80 4.2, 9.7) and the analytic results of Ze80 9.3. It uses no segment, cuspidal
or other derivative formula, and no part of task
`8e5b4563-0365-41c7-b134-70f2a0b36292`.

The Lean files of the full closure and this module were searched for each excluded
declaration name and task-ID prefix in the task's exclusion union. These are tasks
`23189526`, `f3a69bc8`, `aca8805b`, `23e98d90`, `2ae5cbe5`, `8364e73f`, `3bfb61fa`,
`ebea9a8a`, `20e4e1c6`, `52e97845`, `1cb45da2`, `cd8ab97c`, `bf433f0a`,
`30341ae4`, `8252833d`, `5eece9e8`, `67279e36`, `4ca79bbd`, `e3634665`,
`ed48ae06`, `55ad1e10`, `b95105c6`, `92aea10f`, `8e5b4563`, `ff4738d8`,
`3c9849a4`, `ab61f565` and `77ea7de9`. The declaration names are
`AdjacentUnlinkedSegmentSocleSwap`, `TwoSegmentSocleCommutation`,
`SquareIntegrableLanglandsClassification`, `GenericSegmentProductUniqueness`,
`SegmentSpecialEssentialSquareIntegrability`, `OrderedMultisegmentSocleExistence`,
`MultisegmentSocleExhaustion`, `SegmentSocleProductIrreducibility`,
`SegmentFullJacquetFormula`, `SegmentHeadJacquetFormula`,
`SegmentSocleJacquetFormula`, `SegmentSpecialJacquetExponentNormFormula`,
`MirabolicDerivativeDetection` and `MirabolicDerivativeVanishing`. The search
also covered the words `Segment`, `Multisegment` and `Ze80`. There were no
matches. The only occurrences of `Zelevinsky` are the BZ77 attributions in the
module docstrings of `MirabolicCharacter` and `MirabolicMinus`. Hence the proof
depends neither directly nor transitively on any excluded conclusion, its proof
successors or its consequences. The same holds for the strong-indecomposability,
ordered-socle and nonadjacent-product consumers of this detection clause, and for
the two-supercuspidal product-structure conclusion of task
`ab61f565-1427-4746-ba77-46097563e962`.

This audit concerns this proof only. Lower inputs reused later by other tasks
need their own independence audit.
