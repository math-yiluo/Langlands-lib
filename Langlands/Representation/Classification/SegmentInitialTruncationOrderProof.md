# Initial truncation preserves nonprecedence

Authors: Worker 700 (proof draft) and Worker 904 (final revision).

## Target

The theorem `Langlands.Classification.segmentInitialTruncationOrder` proves
exactly `Langlands.Classification.SegmentInitialTruncationOrder.{uF,uV} F T`
from the published module
`Langlands.Representation.Classification.SegmentInitialTruncationOrderStatement`.
Its outer telescope is `{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)`
`(T : F.TopologicalData)`. The field universe `uF` and the cuspidal-carrier
universe `uV` stay independent. The statement, the truncations
`Segment.dropLast` and `Segment.dropLastList`, and every other definition
used are imported unchanged from the published Library.

The target assumes `CuspidalIntegralTwistFreeness.{uF,uV} F T` and concludes
two clauses:

1. For segments `Δ`, `Γ` with `Δ.dropLast = some Δ'` and
   `Γ.dropLast = some Γ'`, if `Δ'` precedes `Γ'` then `Δ` precedes `Γ`.
2. For every list `l` of segments, empty or with repetitions, if
   `T.IsPrecedenceOrderedList l` then
   `T.IsPrecedenceOrderedList (Segment.dropLastList l)`.

The freeness antecedent is kept, no hypothesis is added, and the list is the
supplied list with the actual optional truncation applied.

## Implemented proof

**Coordinates of the original segment.** The private lemma
`coordinates_of_dropLast` states: if `Δ.dropLast = some Δ'` and `Δ'` has
integral coordinates `[a,b]` on the twist line through `ρ`, then `Δ` has
coordinates `[a,b+1]` on the same line. Here
`Segment.HasIntegralCoordinates Δ ρ a b` means
`Δ.base = ρ.twist a` and `b = a + Δ.length - 1`. The proof splits on
`1 < Δ.length`.

- If `1 < Δ.length`, then `Segment.dropLast_of_one_lt` rewrites the
  truncation to `some (Δ.dropLastNonempty h)`. Injectivity of `some`
  identifies `Δ'` with it. Its base is definitionally `Δ.base` and its length
  is `Δ.length - 1`. The base condition carries over unchanged. The endpoint
  equation `b = a + (Δ.length - 1) - 1` gives `b + 1 = a + Δ.length - 1` by
  `omega`, using `1 < Δ.length` for the natural subtraction.
- Otherwise `Segment.dropLast` unfolds to `none`. This contradicts the
  hypothesis `Δ.dropLast = some Δ'`, and `simp` closes the case.

**Precedence reflection (clause 1).** Assume `Δ'` precedes `Γ'`. The
published theorem `Segment.hasIntegralCoordinates_self` puts `Δ'` at
coordinates `[0, Δ'.length - 1]` on the line through `Δ'.base`.
`Segment.HasIntegralCoordinates.of_precedes_right` turns the precedence into
coordinates `[c,d]` for `Γ'` on the same line. On a free twist line,
`Segment.HasIntegralCoordinates.precedes_iff` translates precedence into
`Segment.IntervalPrecedes a b c d`, that is, `a < c`, `c ≤ b + 1` and
`b < d`. The coordinate lemma gives coordinates `[a,b+1]` for `Δ` and
`[c,d+1]` for `Γ`. The required configuration `a < c`, `c ≤ (b+1) + 1`,
`b + 1 < d + 1` follows from the three inequalities by `omega`.
`Segment.HasIntegralCoordinates.precedes_of_intervalPrecedes`, again under
the freeness hypothesis, then returns `Δ.Precedes Γ`.

**List clause (clause 2).** `T.IsPrecedenceOrderedList l` unfolds to
`l.Pairwise (fun Δ Γ => ¬ Δ.Precedes Γ)`, and `Segment.dropLastList l` unfolds
to `l.filterMap Segment.dropLast`. The proof uses Mathlib's
`List.Pairwise.filterMap`. Given an original pair `Δ`, `Γ` in list order
that does not precede, and survivors `Δ' ∈ Δ.dropLast` and
`Γ' ∈ Γ.dropLast`, `Option.mem_def` turns membership into
`Δ.dropLast = some Δ'` and `Γ.dropLast = some Γ'`. A precedence `Δ'` before
`Γ'` would give `Δ` before `Γ` by clause 1, a contradiction. Because
`List.Pairwise.filterMap` holds for arbitrary lists, the proof covers the
empty list and keeps repeated survivors. Singleton segments, whose
truncation is `none`, are removed with no special case.

## Source and provenance

The result is an internal combinatorial consequence of the segment
conventions of Zelevinsky, *Induced representations of reductive p-adic
groups II. On irreducible representations of GL(n)*, Ann. Sci. ENS (4) 13
(1980), 165-210. Registered source `zelevinsky-1980-induced-ii`, SHA256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
Worker 904 read the following passages in the registered PDF:

- §3.5, printed p.182 / PDF p.19, defines `Δ⁻ = Δ \ {ρ'}` for
  `Δ = [ρ, ρ']`, with `Δ⁻` empty for a singleton. This is the published
  `Segment.dropLast`.
- §4.1, printed p.184 / PDF p.21, defines linked segments and precedence:
  `Δ₁` precedes `Δ₂` when they are linked and `ρ₂ = ν^k ρ₁` with `k > 0`.
  The same paragraph notes that, for non-singleton segments, `Δ₁⁻` and `Δ₂⁻`
  are linked exactly when `Δ₁` and `Δ₂` are linked but not juxtaposed.
- §6.2, printed p.188 / PDF p.25, derives 6.1(a) by passing to the highest
  derivative `⟨Δ₁⁻⟩ × … × ⟨Δᵣ⁻⟩` and inducting on `n`. This step needs the
  truncated sequence to keep the nonprecedence order, which is the motivation
  for this lemma.

Zelevinsky does not state this lemma as a separately numbered result.
The proof here does not follow the source: it uses the published
integer-coordinate criterion for precedence. No errata for this article were
found in the central library or the literature index. The proof involves no
representations, derivatives, homogeneity, product irreducibility or
classification, and it proves no integral-twist-freeness result.

## Import audit and independence

The module imports exactly
`Langlands.Representation.Classification.SegmentInitialTruncationOrderStatement`
and `Langlands.Representation.Classification.SegmentIntervalLinkage`. Its
complete transitive project import closure has 53 modules, listed below. All
53 are byte-identical, Lean and Markdown, to the published Library at
commit `84ad0affe3e3e8feae73b57da624fc1f16a6923b`. Worker 700's earlier
audit listed 52. Since then, the Library added
`Langlands.Representation.Jacquet.CharacterTwistEquiv`, now imported by
`Classification.SupercuspidalTwist`. That module identifies Jacquet quotients
under a character trivial on the radical and is pure linear algebra.

The classification modules in the closure are `ConstituentRelations`,
`CuspidalIntegralTwistFreenessStatement`, `SegmentInitialTruncation`,
`SegmentInitialTruncationOrderStatement`, `SegmentIntegralCoordinates`,
`SegmentIntervalLinkage`, `Segments`, `Supercuspidal` and
`SupercuspidalTwist`. The freeness module only states a proposition, which
this proof takes as a hypothesis. The other modules supply local-field
topology and normalization, block groups, smooth representations, twists,
induction definitions, tensor constructions and Jacquet coinvariants. The
endpoint theorems used from `SegmentIntervalLinkage` and
`SegmentIntegralCoordinates` rely only on integral twist identities, finite
interval arithmetic and support computations.

No module in the closure contains the conclusion, a proof successor or a
transitive proof dependency of any of these: ordered-socle existence, socle
exhaustion, analytic segment classification, unlinked segment-socle product
irreducibility, the final segment-socle irreducibility criterion,
`AdjacentUnlinkedSegmentSocleSwap`, `TwoSegmentSocleCommutation`, the
special-head product irreducibility criterion, special-head exhaustion,
ordered special-head existence, quotient coverage, tempered block
uniqueness, `SquareIntegrableLanglandsClassification`, square-integrable
exhaustion, regular exhaustion, `GenericSegmentProductUniqueness`, ordered
special-segment conversion and forward special-segment essential
square-integrability.

- `Langlands.Group.GL.Basic`
- `Langlands.Group.GL.BlockModulus`
- `Langlands.Group.GL.Blocks`
- `Langlands.Group.GL.NormalizedCharacter`
- `Langlands.Group.GL.Padic`
- `Langlands.Group.GL.PadicBlocks`
- `Langlands.LocalField.Canonical`
- `Langlands.LocalField.Definitions`
- `Langlands.LocalField.Normalization.Definitions`
- `Langlands.LocalField.Normalization.Proof`
- `Langlands.LocalField.Normalization.Statement`
- `Langlands.LocalField.Topology`
- `Langlands.Representation.Category.Basic`
- `Langlands.Representation.Category.Twist`
- `Langlands.Representation.Classification.ConstituentRelations`
- `Langlands.Representation.Classification.CuspidalIntegralTwistFreenessStatement`
- `Langlands.Representation.Classification.SegmentInitialTruncation`
- `Langlands.Representation.Classification.SegmentInitialTruncationOrderStatement`
- `Langlands.Representation.Classification.SegmentIntegralCoordinates`
- `Langlands.Representation.Classification.SegmentIntervalLinkage`
- `Langlands.Representation.Classification.Segments`
- `Langlands.Representation.Classification.Supercuspidal`
- `Langlands.Representation.Classification.SupercuspidalTwist`
- `Langlands.Representation.Induction.BlockFactors`
- `Langlands.Representation.Induction.Definitions`
- `Langlands.Representation.Induction.Parabolic`
- `Langlands.Representation.Jacquet.CharacterTwistEquiv`
- `Langlands.Representation.Jacquet.Coinvariants`
- `Langlands.Representation.Jacquet.PositiveCharacter`
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
- `Langlands.Representation.Tensor.Finite`
- `Langlands.Representation.Twist.AdmissibilityProof`
- `Langlands.Representation.Twist.AdmissibilityStatement`
- `Langlands.Representation.Twist.AlgebraProof`
- `Langlands.Representation.Twist.AlgebraStatement`
- `Langlands.Representation.Twist.Definitions`
- `Langlands.Representation.Twist.RealPower`
- `Langlands.Representation.Twist.SmoothProof`
- `Langlands.Representation.Twist.SmoothStatement`
- `Langlands.Representation.Twist.SubquotientDefinitions`
- `Langlands.Representation.Twist.SubquotientProof`
- `Langlands.Representation.Twist.SubquotientStatement`
- `Langlands.Representation.Unitary.Basic`

## Development checks

Development check `98fe7b5e-30bc-40ac-b129-59ca689b0767` compiled this module
in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` with no diagnostics. It
inspected `segmentInitialTruncationOrder` as a theorem with universe
parameters `uF` and `uV` and axioms `propext`, `Classical.choice` and
`Quot.sound` only. Private check `048d8790-fd45-4017-b147-492a785c5a10`
also compiled a separate unsubmitted file. That file assigns the unapplied
constant `@segmentInitialTruncationOrder.{uF,uV}` to the complete telescope
`∀ {p} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
SegmentInitialTruncationOrder.{uF,uV} F T`. These development checks are
not independent acceptance, exact-target validation or publication.
