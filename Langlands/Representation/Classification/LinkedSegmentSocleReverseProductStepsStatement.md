# Steps (1) and (2) of Zelevinsky's Proposition 4.6 for segment socles

Authors: Worker 999 and Worker 219 (planning draft), for task
`7ff2a1e9-89dc-439e-a861-a567b3db92bf` (published by Worker 219 as a
prerequisite of the exact proof task `a55c4267-7e3a-43f6-8bb1-ce319e1d0aa9`).

This module contains two Prop-valued definitions and no theorems:

- `Langlands.Classification.JuxtaposedSegmentSocleReverseProductStructure.{uF,uV} F T`,
  Zelevinsky 1980, Proposition 4.6, restricted to juxtaposed segments (step (1)
  of its proof);
- `Langlands.Classification.LinkedSegmentSocleReverseProductQuotientHom.{uF,uV} F T`,
  the nonzero intertwining map `⟨Δ⟩ × ⟨Δ'⟩ → ⟨Δ ∪ Δ'⟩ × ⟨Δ ∩ Δ'⟩` for every
  precedence pair (step (2) of its proof).

**Both propositions are unproved by this contribution.** They are definitions
of statements. They are steps of the exact proof task
`a55c4267-7e3a-43f6-8bb1-ce319e1d0aa9` of the published
`Langlands.Classification.LinkedSegmentSocleReverseProductStructure` (the full
Proposition 4.6) in `Langlands.Representation.Classification.SegmentSocleCriterionHalvesStatement`.
Their proofs are separate proof tasks.

## Common parameters

Both definitions are parametrized exactly like
`LinkedSegmentSocleReverseProductStructure`: any `p : ℕ` with
`[Fact p.Prime]`, any `F : PadicField.{uF} p` and any supplied
`T : F.TopologicalData`. Each body begins with `letI := T.topology`. The field
universe `uF` and the segment-base universe `uV` are independent; the segments
are `T.Segment.{uV,uF}`, the data are `T.SegmentProductDatum.{uV,uF} n`, and
the blocks and induced representations have carriers in `Type (max uF uV)`.
Both definitions return `Prop` with level parameters `uF uV`, and both
elaborate at `.{uF, max uF uV}`.

The module imports the unchanged `Classification.LanglandsData`,
`Classification.SegmentReplacementInversions` and
`Filtration.ObjectDefinitions`, the imports of
`SegmentSocleCriterionHalvesStatement`.

## Index convention

For `d : T.SegmentProductDatum.{uV,uF} n` and `h₂ : d.length = 2`, write
`Δ = d.segments ⟨0, _⟩` and `Δ' = d.segments ⟨1, _⟩`; the bounds are
discharged by `omega` from `h₂`. Then `π = d.induced` is the normalized product
`d.blocks 0 × d.blocks 1`, that is Ze80's `⟨Δ⟩ × ⟨Δ'⟩` when
`d.HasSegmentSocles`. The precedence hypothesis is
`(d.segments ⟨1, _⟩).Precedes (d.segments ⟨0, _⟩)`, that is "`Δ'` precedes
`Δ`", as in Ze80 4.6 and in `LinkedSegmentSocleReverseProductStructure`.

## Exact propositions

### 1. `JuxtaposedSegmentSocleReverseProductStructure`

For every `n : ℕ`, every `d : T.SegmentProductDatum.{uV,uF} n` and every
`h₂ : d.length = 2`, if `d.HasSegmentSocles`, `Δ'.Precedes Δ` and
`Δ'.IsJuxtaposed Δ`, there exist `U : T.Segment.{uV,uF}`,
`I : Option (T.Segment.{uV,uF})` and `e : T.SegmentProductDatum.{uV,uF} n`
such that, in this order,

1. `Δ.IsUnionIntersectionReplacement Δ' U I`: `U.support` is the union of the
   supports, and either `I = none` and the supports are disjoint, or
   `I = some J` and `J.support` is their intersection;
2. `List.ofFn e.segments = U :: I.toList`;
3. `e.HasSegmentSocles`;
4. `Representation.IsIrreducible e.induced.representation`;
5. there is `s : ObjectRepFiltration (Rep.of d.induced.representation) 2` with
   `s.HasSimpleFactors`, an actual `Representation.Equiv` from
   `(s.gradedRepresentation 1).ρ` to `e.induced.representation`, no such
   equivalence from `(s.gradedRepresentation 0).ρ`, and such that every
   irreducible `K : Subrepresentation d.induced.representation` equals
   `s.subrepresentation 1`.

This is the body of `LinkedSegmentSocleReverseProductStructure` with the one
extra hypothesis `Δ'.IsJuxtaposed Δ`, placed after the precedence hypothesis.
The conclusion is copied verbatim. So the juxtaposed case of the full
proposition is a direct application: given a proof `h` of statement 1 and
data `n d h₂ hs hp hj`, the term `h n d h₂ hs hp hj` has exactly the type that
`LinkedSegmentSocleReverseProductStructure` requires. Conversely, a private
check (not part of this module) derives statement 1 from the full proposition
by `fun n d h₂ hs hp _ => h n d h₂ hs hp`.

`Segment.IsJuxtaposed` is linked with disjoint supports, so in fact `I = none`
and `e` has the single segment `Δ ∪ Δ'`. The general `U`/`I`/`e` shape is
kept anyway, so that the conclusion is literally that of the full
proposition.

With `ObjectRepFiltration A 2` the published chain `0 = S₀ ≤ S₁ ≤ S₂ = A` of
invariant subspaces, `s.subrepresentation k = S_k` and
`s.gradedRepresentation k = S_(k+1)/S_k`. So graded piece 0 is the unique
irreducible submodule `ω₀ = S₁` of `π`, and graded piece 1 is `π/ω₀`. Clause 5
says that `π` has length two, that `π/ω₀ ≅ ω = e.induced`, that `ω₀ ≇ ω`, and
that `ω₀` is the unique irreducible subrepresentation of `π`.

### 2. `LinkedSegmentSocleReverseProductQuotientHom`

For every `n : ℕ`, every `d : T.SegmentProductDatum.{uV,uF} n` and every
`h₂ : d.length = 2`, if `d.HasSegmentSocles` and `Δ'.Precedes Δ`, then for
all `U : T.Segment.{uV,uF}`, `I : Option (T.Segment.{uV,uF})` and
`e : T.SegmentProductDatum.{uV,uF} n` with
`Δ.IsUnionIntersectionReplacement Δ' U I`,
`List.ofFn e.segments = U :: I.toList` and `e.HasSegmentSocles`, there is
`f : d.induced.representation.IntertwiningMap e.induced.representation` with
`f ≠ 0`.

This is Ze80's `Hom(π, ω) ≠ 0`, with `ω = e.induced`. It is stated for every
precedence pair, juxtaposed or not, and for every socle datum `e` of the
union followed by the optional intersection, not just for one. It has no
irreducibility or surjectivity conclusion. The Hom form
`∃ f : _.IntertwiningMap _, f ≠ 0` is the one of the published
`Filtration.NonzeroHomCommonSubquotientStatement`.

## Conventions

The unchanged imported definitions use normalized parabolic induction from
the standard upper block parabolic, positive half-modulus covariance and right
translation. `T.IsSegmentSocle Δ π` is the increasing-induction socle
convention of Ze80 §3.1: for some supercuspidal representative `A` of the
base class of `Δ`, `π` is irreducible, embeds into
`T.segmentInduced A Δ.length _ = i(A, νA, …, ν^(m-1)A)`, and every irreducible
embedding into it has the same image. `d.HasSegmentSocles` requires this of
every block; the blocks are supplied, not chosen. This is not the special head
(`HasSegmentHeads`).

`Segment.IsLinked`, `Segment.IsJuxtaposed` (linked with disjoint supports)
and `Segment.Precedes` (linked, and the base of the second is a positive
integral `ν`-twist of the base of the first) are Ze80 §4.1's notions, from
`Classification/Segments.lean`. `Segment.IsUnionIntersectionReplacement` is
from `Classification/SegmentReplacementInversions.lean`.

The definitions preserve repeated and equal segments, every prime, field,
supplied topology and both universes. They contain no finite-length,
derivative, homogeneity, genericity, commutation, irreducibility or existence
premise.

## Source correspondence

A. V. Zelevinsky, *Induced representations of reductive p-adic groups II. On
irreducible representations of GL(n)*, Ann. Sci. ENS (4) 13 (1980),
pp.165–210. Registered source `zelevinsky-1980-induced-ii`, SHA256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`. Printed
page = zero-based PDF index + 164. No errata note was found.

- Proposition 2.10, printed p.180 (index 16): for an ordering `λ` of the
  cuspidal representations `ρ₁, …, ρ_r` of §2.1, the product `π(λ)` has the
  unique irreducible submodule `ω(Γ(λ))`, where `Γ(λ)` is the orientation of
  the graph `Γ` of §2.2 determined by `λ`.
- §3.1, printed pp.180–181 (indices 16–17): a segment is
  `Δ = [ρ, ρ'] = {ρ, νρ, …, ρ'}`, and `⟨Δ⟩` is the irreducible representation
  of the orientation `ρ → νρ → ⋯ → ρ'`, that is, by 2.10, the unique
  irreducible submodule of `ρ × νρ × ⋯ × ρ'`. This is the socle convention
  above.
- §4.1, printed p.184 (index 20): linked, juxtaposed (linked with
  `Δ₁ ∩ Δ₂ = ∅`) and precedes.
- §4.6, printed p.185 (index 21): `Δ∪ = Δ ∪ Δ'`, `Δ∩ = Δ ∩ Δ'`
  (`Δ∩ = ∅` when juxtaposed), `ω = ⟨Δ∪⟩ × ⟨Δ∩⟩`, irreducible by 4.2
  (2)⇒(1). **Proposition:** if `Δ'` precedes `Δ` and `π = ⟨Δ⟩ × ⟨Δ'⟩`, then
  `π` has the unique irreducible submodule `ω₀`, `ω₀ ≇ ω` and `π/ω₀ ≅ ω`.
- Proof, step (1), printed pp.185–186 (indices 21–22): if `Δ` and `Δ'` are
  juxtaposed, write `Δ' = [ρ, ν^(p-1)ρ]`, `Δ = [ν^p ρ, ν^(r-1)ρ]` with
  `0 < p < r`, and apply §2 with `ρ_i = ν^(i-1)ρ`. By 1.6 and 3.1 the
  irreducible constituents of `π` are `ω(Γ₁)` and `ω(Γ₂)`, for the
  orientations `ρ₁ → ⋯ → ρ_r` and the one reversing the edge between
  `ρ_p` and `ρ_(p+1)`. By Proposition 2.10 (printed p.180, index 16), `π` has
  the unique irreducible submodule `ω₀ = ω(Γ₂)`, and `ω(Γ₁) = ⟨Δ∪⟩ = ω`.
  **Statement 1 is the Proposition in this case.**
- Proof, step (2), printed p.186 (index 22): if `Δ` and `Δ'` are linked but not
  juxtaposed, then `Hom(π, ω) ≠ 0`. Frobenius reciprocity (1.1) reduces this
  to `Hom(σ, ⟨Δ∪⟩ ⊗ ⟨Δ∩⟩) ≠ 0` with `σ = r_(γ,(n))(π)`; the geometric lemma
  (Corollary 1.3), 3.4 and 1.5 give a quotient
  `σ' = (⟨Δ⟩ × ⟨Δ' \ Δ∩⟩) ⊗ ⟨Δ∩⟩` of `σ`; and step (1), for the juxtaposed
  pair `Δ`, `Δ' \ Δ∩`, gives a quotient `⟨Δ∪⟩` of the first factor.
  **Statement 2 is this claim**, extended to the juxtaposed case, where it
  follows from statement 1 (the quotient map `π ↠ π/ω₀ ≅ ω` is nonzero).
- Step (3), printed p.186, compares highest derivatives. It is not stated
  here.

The Lean statements differ from the source only in packaging: the blocks are
supplied socles rather than the source's `⟨Δ⟩`, which agree up to
isomorphism; statement 1 asserts the existence of a socle datum `e` for the
union instead of naming `⟨Δ∪⟩`; statement 2 quantifies over all such data;
and `ω₀`, `π/ω₀` are an actual two-step filtration with simple graded pieces.

## Intended use

This module does not state or prove the assembly. The proof of
`LinkedSegmentSocleReverseProductStructure` (task
`a55c4267-7e3a-43f6-8bb1-ce319e1d0aa9`) is planned as a strong induction on
`n`. In the juxtaposed case it applies statement 1. Otherwise statement 2,
with the irreducibility of `ω` (`UnlinkedSegmentSocleProductIrreducible`),
gives a surjection `π ↠ ω`, and the derivative comparison of step (3)
finishes.

## Development checks

These private `lean_check` diagnostics in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` are development evidence, not
acceptance:

- `8a6defe0-fdc7-4fa1-bf41-de572d87a8c1` and
  `558b5964-c4ed-4ff4-8233-56bf1e440456`: this module compiles with no errors
  or warnings, and both definitions return `Prop` with level parameters
  `uF uV`.
- `d6f2d43c-0f22-46e3-8eb8-02415bda3a4c`: a private check module, not part of
  this contribution, proves statement 1 from
  `LinkedSegmentSocleReverseProductStructure` by
  `fun n d h₂ hs hp _ => h n d h₂ hs hp`. Conversely, it derives the juxtaposed
  case of the full proposition from statement 1 by
  `exact h n d h₂ hs hp hj`, with the full proposition's conclusion written
  out verbatim as the goal. For proofs `h` of statement 1 and `hfull` of the
  full proposition, it also checks that `h n d h₂ hs hp hj` is accepted with
  the type of `hfull n d h₂ hs hp`. Finally, it checks that both statements
  elaborate at `.{uF, max uF uV}`.

## Proof successors and independence

After acceptance and publication, two exact `lean.proof@1` tasks will prove
statement 1 and then statement 2. The proof of statement 2 may import the
published proof of statement 1.

- Statement 1. Source route: Ze80 4.6 step (1), via §2 (2.2–2.10), 1.6 and
  3.1. An independently proved replacement is also acceptable.
- Statement 2. Source route: Ze80 4.6 step (2). It uses Frobenius
  reciprocity (1.1), the normalized geometric lemma
  `Langlands.Geometric.PadicGeometricLemmaTheorem`, the socle Jacquet
  formula `Langlands.Classification.SegmentSocleJacquetFormula` (Ze80 3.4),
  1.5, and the quotient clause of statement 1 for the juxtaposed pair `Δ`,
  `Δ' \ (Δ ∩ Δ')`. In the juxtaposed case, statement 2 follows directly from
  statement 1.

Neither step needs derivatives.

These statements are upstream inputs of the proof of
`LinkedSegmentSocleReverseProductStructure`. Their proofs must preserve
direct and transitive independence from every item below. This covers their
conclusions, proof successors and transitive proof dependencies:

- `LinkedSegmentSocleReverseProductStructure` and task
  `a55c4267-7e3a-43f6-8bb1-ce319e1d0aa9`;
- `LinkedSegmentSoclePairReducible` and task
  `8fa9f68b-fa1b-431a-97f6-5b163964d1fc`;
- `SegmentSocleProductIrreducibility` and task
  `2ae5cbe5-0701-4509-88a0-db8cbeb35be4`;
- adjacent socle commutation `AdjacentUnlinkedSegmentSocleSwap`, task
  `e3634665-571b-4852-9f4c-bab8a1053434` and its proof successor
  `cded83f3-df9c-4018-bc61-dc54f5c1f9ab`;
- `TwoSegmentSocleCommutation`, tasks
  `426911b4-6620-413f-8065-04b25287f3bd` and
  `66e3b87c-647e-41e4-af18-df4d436765f0`;
- `LinkedSegmentSocleGluing`, tasks `c84cd52c-3ff3-4024-be50-8b84dd480888`
  and `6780b79c-9526-46aa-b8b4-00377d68b1ea`;
- `OrderedMultisegmentSocleExistence` and task
  `23189526-80b0-4828-a6d4-7ebec2cbeef5`;
- socle exhaustion, task `f3a69bc8-7312-4f82-8a7d-ea3c8188cb63`;
- segment analytic classification, task
  `aca8805b-054f-4d56-8045-12db7f623404`;
- special-head multisegment exhaustion, task
  `3bfb61fa-1129-4fc9-83fd-7fcfec22106e`;
- ordered special-head existence, task `ebea9a8a-9b21-4208-aa31-98c2dea1f8a3`;
- quotient coverage, task `20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584`;
- tempered block uniqueness, task `52e97845-36bb-457d-b76f-70753334b88c`;
- `SquareIntegrableLanglandsClassification` and task
  `1cb45da2-7007-4351-a694-594fb148b8d1`;
- square-integrable exhaustion, task `cd8ab97c-0b78-4bce-97c4-d307a28159a4`;
- regular exhaustion, task `bf433f0a-921a-428c-b0c0-6475438125ac`;
- the special-head criterion `SegmentHeadProductIrreducibility`, task
  `8364e73f-14ec-4d14-8f2b-1555a7c1ce95`.

The proofs may import the published proofs of
`UnlinkedSegmentSocleProductIrreducible` (task
`23e98d90-6055-4e35-91a9-b0f5d8a84961`) and of
`TwoFactorProductConstituentCommutativity` (task
`1b2016bd-4fd3-4ec6-a1b4-ec0788046ed9`). Shared lower inputs, such as the
geometric lemma, Jacquet formulas, cuspidal support and finite length, may be
reused only after their direct and transitive independence has been checked.
Proposition definitions, citations, conditional assemblies and pending tasks
are not proof evidence.
