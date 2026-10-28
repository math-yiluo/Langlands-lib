# The two halves of Zelevinsky's segment socle irreducibility criterion

Author: Worker 758, for task `16045335-62c9-4da7-b38f-88579104274b`
(revision 2, published by Worker 250).

This module contains three Prop-valued definitions and no theorems:

- `Langlands.Classification.UnlinkedSegmentSocleProductIrreducible.{uF,uV} F T`,
  the implication (2)⇒(1) of Zelevinsky 1980, Theorem 4.2;
- `Langlands.Classification.LinkedSegmentSocleReverseProductStructure.{uF,uV} F T`,
  the full Zelevinsky 1980, Proposition 4.6;
- `Langlands.Classification.LinkedSegmentSoclePairReducible.{uF,uV} F T`,
  reducibility of the product of the socles of two linked segments, in either
  order.

**All three propositions are unproved by this contribution.** They are
definitions of statements; their proofs are separate proof tasks.

## Common parameters

Each definition is parametrized like the published
`Langlands.Classification.SegmentSocleProductIrreducibility.{uF,uV} F T`
in `Langlands.Representation.Classification.SegmentGenericStatement`: any
`p : ℕ` with `[Fact p.Prime]`, any `F : PadicField.{uF} p` and any supplied
`T : F.TopologicalData`. Each body begins with `letI := T.topology`. The
field universe `uF` and the segment-base universe `uV` are independent; the
segments are `T.Segment.{uV,uF}`, the data are `T.SegmentProductDatum.{uV,uF}`,
and the blocks and induced representations have carriers in
`Type (max uF uV)`. All three definitions return `Prop` with level parameters
`uF uV`.

A datum `d : T.SegmentProductDatum.{uV,uF} n` consists of a length
`d.length`, segments `d.segments : Fin d.length → T.Segment`, a proof that
their degrees add up to `n`, and actual blocks `d.blocks i`, smooth complex
representations of `GL_(deg Δ_i)(F)`. `d.induced` is the normalized product
`d.blocks 0 × ⋯ × d.blocks (r-1)`, in this order, and `d.multisegment` is the
multiset of the segments with multiplicities.

## Exact propositions

### 1. `UnlinkedSegmentSocleProductIrreducible`

For every `n : ℕ` and every `d : T.SegmentProductDatum.{uV,uF} (n + 1)`, if
`d.HasSegmentSocles` and `d.multisegment.IsUnlinked`, then
`Representation.IsIrreducible d.induced.representation`.

`Multisegment.IsUnlinked a` says that no two members of `a` are linked
(`Segment.IsLinked`). Repeated and equal segments are allowed; a segment is
never linked to itself (`Segment.not_isLinked_self`). The ordering of the
segments is arbitrary. The rank `n + 1` matches
`SegmentSocleProductIrreducibility`.

### 2. `LinkedSegmentSocleReverseProductStructure`

For every `n : ℕ`, every `d : T.SegmentProductDatum.{uV,uF} n` and every
`h₂ : d.length = 2`, write `Δ = d.segments ⟨0, _⟩` and
`Δ' = d.segments ⟨1, _⟩` (the bounds are discharged by `omega` from `h₂`),
so that `R = d.induced` is `⟨Δ⟩ × ⟨Δ'⟩`. If `d.HasSegmentSocles` and
`Δ'.Precedes Δ`, there exist `U : T.Segment.{uV,uF}`,
`I : Option (T.Segment.{uV,uF})` and `e : T.SegmentProductDatum.{uV,uF} n`
such that, in this order,

1. `Δ.IsUnionIntersectionReplacement Δ' U I`, that is,
   `U.support = Δ.support ∪ Δ'.support`, and either `I = none` and
   `Δ.support ∩ Δ'.support = ∅`, or `I = some J` and
   `J.support = Δ.support ∩ Δ'.support`;
2. `List.ofFn e.segments = U :: I.toList`: `e` lists the union segment,
   followed by the intersection segment when it is nonempty;
3. `e.HasSegmentSocles`;
4. `Representation.IsIrreducible e.induced.representation` (this is Ze80's
   `ω = ⟨Δ ∪ Δ'⟩ × ⟨Δ ∩ Δ'⟩`);
5. there is `s : ObjectRepFiltration (Rep.of d.induced.representation) 2`
   with
   - `s.HasSimpleFactors` (both graded pieces are irreducible);
   - `Nonempty ((s.gradedRepresentation 1).ρ.Equiv e.induced.representation)`,
     that is `R/ω₀ ≅ ω`;
   - `¬ Nonempty ((s.gradedRepresentation 0).ρ.Equiv e.induced.representation)`,
     that is `ω₀ ≇ ω`;
   - every `K : Subrepresentation d.induced.representation` with
     `Representation.IsIrreducible K.toRepresentation` equals
     `s.subrepresentation 1`: `ω₀` is the unique irreducible
     subrepresentation of `R`.

Here `ObjectRepFiltration A 2` is the published chain `0 = S₀ ≤ S₁ ≤ S₂ = A`
of invariant subspaces of the actual representation `A`,
`s.subrepresentation k` is `S_k`, and `s.gradedRepresentation k` is the actual
quotient `S_(k+1)/S_k`. So `ω₀ = S₁ ≅ s.gradedRepresentation 0` and
`R/ω₀ = s.gradedRepresentation 1`. `Representation.Equiv` is an invertible
equivariant complex-linear map. All of these are actual subrepresentations and
actual isomorphisms, not Grothendieck-group identities.

The `U`/`I`/`e` conventions are copied from the published
`Langlands.Classification.LinkedSegmentSocleGluing` in
`LinkedSegmentSocleGluingStatement`. The replacement there is written with
the preceding segment first; the support conditions of
`IsUnionIntersectionReplacement` are symmetric up to `Set.union_comm` and
`Set.inter_comm`. A gluing proof applies statement 2 to the reverse datum
`d.permute σ`, where `σ = d.shape.adjacentSwap 0 _`; the segments of
`d.permute σ` are the segments of `d` swapped, and its blocks are the supplied
blocks of `d`, swapped.

### 3. `LinkedSegmentSoclePairReducible`

For every `n : ℕ`, every `d : T.SegmentProductDatum.{uV,uF} n` and every
`h₂ : d.length = 2`, if `d.HasSegmentSocles` and
`(d.segments ⟨0, _⟩).IsLinked (d.segments ⟨1, _⟩)`, then
`¬ Representation.IsIrreducible d.induced.representation`.

There is no precedence premise. Linkage is symmetric (`Segment.IsLinked.symm`),
so this covers the precedence order `⟨Δ⟩ × ⟨Δ'⟩` with `Δ'` preceding `Δ` and
the other order `⟨Δ'⟩ × ⟨Δ⟩`. Statement 3 records only reducibility, in
either order; it does not describe the submodule lattice.

In statements 2 and 3 every natural rank `n` is quantified. Rank zero is
vacuous, since a segment has positive degree.

## Conventions

The unchanged imported definitions use normalized parabolic induction from
the standard upper block parabolic, positive half-modulus covariance and
right translation. For a segment `Δ = [ρ, νρ, …, ν^(m-1)ρ]`, with
`ν = |det|_F` and `ρ` an irreducible supercuspidal representation of
`GL_r(F)`, the published `T.IsSegmentSocle Δ π` says: for some supercuspidal
representative `A` of the base class of `Δ`, `π` is irreducible, embeds into
the increasing induction `T.segmentInduced A Δ.length _`, that is
`i(A, νA, …, ν^(m-1)A)` on `GL_(mr)(F)`, and every irreducible embedding
into it has the same image (`Classification.IsIrreducibleSocle`). This is the
increasing-induction socle convention of Ze80 §3.1: `⟨Δ⟩` is the unique
irreducible submodule of `ρ × νρ × ⋯ × ρ'`. `d.HasSegmentSocles` requires
this of every block, `T.IsSegmentSocle (d.segments i) (d.blocks i)`. It is not
the special head (`HasSegmentHeads`, the unique irreducible quotient of the
same induction). The definitions assume neither existence of socles for every
segment nor a choice of them; the blocks are supplied.

`Segment.IsLinked Δ₁ Δ₂` means that neither support contains the other and
their union is the support of a segment. `Segment.Precedes Δ₁ Δ₂` means that
they are linked and the base of `Δ₂` is the twist of the base of `Δ₁` by a
positive integral power of `ν`. These are Ze80 §4.1's notions.

The definitions preserve repeated and equal segments, every ordering, every
prime, field, supplied topology and both universes. They contain no
finite-length, derivative, homogeneity, genericity, commutation or existence
premise.

## Source correspondence

A. V. Zelevinsky, *Induced representations of reductive p-adic groups II. On
irreducible representations of GL(n)*, Ann. Sci. ENS (4) 13 (1980),
pp.165–210. Registered source `zelevinsky-1980-induced-ii`, SHA256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`, file
`/home/taskhub/central-library/Zelevinsky--Induced representations of reductive p-adic groups II, irreducible representations of GL(n)--1980.pdf`.
Page references are printed pages, with zero-based PDF indices.

- §3.1, printed pp.180–181 (indices 16–17): a segment is
  `Δ = [ρ, ρ'] = {ρ, νρ, …, ν^k ρ = ρ'}`; `⟨Δ⟩` is "the unique irreducible
  submodule of `ρ × νρ × … × ρ'`" (by 2.10). This is the socle convention
  above.
- Theorem 3.5, printed p.182 (index 18): exactly one derivative `⟨Δ⟩^(k)`
  with `k > 0` is nonzero, and it equals `⟨Δ⁻⟩`, where `Δ⁻ = Δ \ {ρ'}`.
- §4.1, printed p.184 (index 20): linked, juxtaposed and precedes.
- Theorem 4.2, printed p.184 (index 20): `⟨Δ₁⟩ × ⋯ × ⟨Δ_r⟩` is irreducible
  if and only if no `Δ_i`, `Δ_j` are linked. Statement 1 is the implication
  (2)⇒(1), proved in §4.3 (p.184) from Proposition 4.3, using 3.5, the
  Leibniz rule [BZ77, 4.6] and induction on `n`. Proposition 4.3 is proved
  in §§4.4–4.5 (p.185, index 21) with [BZ77, 4.7(b)].
- §4.6, printed pp.185–186 (indices 21–22): with `Δ∪ = Δ ∪ Δ'`,
  `Δ∩ = Δ ∩ Δ'` (`Δ∩ = ∅` when the segments are juxtaposed) and
  `ω = ⟨Δ∪⟩ × ⟨Δ∩⟩`, irreducible by (2)⇒(1) of 4.2. **Proposition 4.6:**
  suppose `Δ'` precedes `Δ` and set `π = ⟨Δ⟩ × ⟨Δ'⟩`; then `π` has the
  unique irreducible submodule `ω₀`, moreover `ω₀ ≇ ω` and `π/ω₀ ≅ ω`.
  Statement 2 is this proposition, together with the irreducibility of `ω`
  stated just before it, with `π = d.induced`, `ω = e.induced` and
  `ω₀ = s.subrepresentation 1`. When the segments are juxtaposed, the
  intersection factor is omitted (`I = none`, and `e` has one segment).
  The source's proof has three steps: (1) the juxtaposed case from §2,
  Proposition 2.10; (2) `Hom(π, ω) ≠ 0` from Frobenius reciprocity (1.1),
  the geometric lemma (1.3), 3.4 and 1.5; (3) comparison of highest
  derivatives, using 3.5, [BZ77, 4.5], Proposition 4.3 and induction on `n`.
- The last sentence of §4.6 (p.186): the implication (1)⇒(2) of 4.2
  "follows immediately from this Proposition". Statement 3 isolates the
  two-factor reducibility that this needs, in both orders.

I. N. Bernstein and A. V. Zelevinsky, *Induced representations of reductive
p-adic groups I*, Ann. Sci. ENS (4) 10 (1977), pp.441–472. Registered source
`bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
§§3–4, printed pp.451–457 (indices 11–17), were read for derivatives
(§3.5), the highest derivative (§4.3), the Leibniz rule (Lemma 4.5 and
Corollary 4.6, p.455) and the support property (Lemma 4.7(b), p.455).

No errata note for either source was found in the public notes.

The Lean statements differ from the source only in packaging: the blocks
are supplied socles rather than the source's `⟨Δ⟩`, which agree up to
isomorphism; statement 2 asserts the existence of a socle datum `e` for
`Δ∪` and `Δ∩` instead of naming `⟨Δ∪⟩ × ⟨Δ∩⟩`; and the submodule
`ω₀` and the quotient `π/ω₀` are expressed by an actual two-step filtration
with simple graded pieces.

## Intended assembly of the full criterion

This module does not state or prove the assembly. Worker 250's proof of
`SegmentSocleProductIrreducibility.{uF,uV} F T` (task
`2ae5cbe5-0701-4509-88a0-db8cbeb35be4`) is intended to combine:

- statement 1, which is the implication from `d.multisegment.IsUnlinked` to
  irreducibility;
- for the converse, a two-factor reduction: if `d.induced` is irreducible
  and `i ≠ j`, then some length-two socle datum with segments
  `d.segments i` and `d.segments j` has an irreducible product. This
  reduction is supplied by the irreducible two-factor case of Ze80 Theorem
  1.9, composition-factor commutativity
  (`Langlands.Classification.TwoFactorProductConstituentCommutativity`, task
  `1b2016bd-4fd3-4ec6-a1b4-ec0788046ed9`), by product regrouping
  (`Langlands.Parabolic.OrderedProductRegrouping`), and by exactness of
  induction. Adjacent factors of an irreducible product commute up to
  isomorphism, so the two factors can be brought to the front. A proper
  nonzero subrepresentation of the front pair would induce a proper nonzero
  subrepresentation of the regrouped product;
- statement 3, which makes that two-factor product reducible when
  `d.segments i` and `d.segments j` are linked. When `i = j` the two segments
  are equal, and `Segment.not_isLinked_self` applies.

A private `lean_check` diagnostic (not part of this contribution) proved
`SegmentSocleProductIrreducibility.{uF,uV} F T` from statement 1,
statement 3 and that two-factor reduction, stated as an explicit hypothesis.
The same diagnostic checked that statement 2 at `.{uF, max uF uV}` produces
`U`, `I` and `e` of exactly the types quantified in
`LinkedSegmentSocleGluing.{uF,uV}`. It also checked that statement 2 applies
to the reverse datum `d.permute σ` of a gluing datum `d`.

## Proof successors and independence

After acceptance and publication, three exact `lean.proof@1` tasks will prove
statements 1, 2 and 3, in that order. The proof of statement 2 may import the
published proof of statement 1. The proof of statement 3 may import the
published proofs of statements 1 and 2. The source routes are the ones above.
Missing prerequisites, such as Ze80 3.5, Proposition 4.3 and the Leibniz rule,
become separate tasks, coordinated with Worker 357's derivative tasks
`74fa48e1-3294-4a36-9b2a-4bc9cf231eeb` and
`a622f240-4846-4086-b34f-f650ba636ee4`.

The statements import only the published `LanglandsData`,
`SegmentReplacementInversions` and `Filtration.ObjectDefinitions` pairs,
unchanged. Their proofs must preserve direct and transitive independence from
every item below. This covers their conclusions, proof successors and
transitive proof dependencies:

- `SegmentSocleProductIrreducibility` and task
  `2ae5cbe5-0701-4509-88a0-db8cbeb35be4`;
- adjacent socle commutation, task `e3634665-571b-4852-9f4c-bab8a1053434`;
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

Proposition definitions, citations, conditional assemblies and pending tasks
are not proof evidence.
