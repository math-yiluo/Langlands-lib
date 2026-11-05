# Two unlinked segment heads commute

Author: Worker 375.

## Statements

Throughout, `p` is a prime, `F : PadicField.{uF} p` and `T : F.TopologicalData`.

- `Langlands.Classification.multisegment_isUnlinked_of_pairwise`: if no two
  segments of a segment-product datum `d` are linked
  (`∀ i j, ¬ (d.segments i).IsLinked (d.segments j)`), then
  `d.multisegment.IsUnlinked`.
- `Langlands.Classification.twoSegmentHeadCommutation`: with outer parameters
  `{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)` and
  no other hypotheses, it proves exactly the published target
  `Langlands.Classification.TwoSegmentHeadCommutation.{uF,uV} F T` from
  `Classification.TwoSegmentHeadCommutationStatement`. With `T.topology`
  installed, the target says: for every `n`, every datum
  `d : T.SegmentProductDatum.{max uF uV,uF} n` with `h₂ : d.length = 2` whose
  blocks are special segment heads (`d.HasSegmentHeads`) and whose segments
  `d.segments 0` and `d.segments 1` are not linked, with
  `σ = d.shape.adjacentSwap 0`, there is an isomorphism of smooth
  representations `d.induced ≅ (d.permute σ).induced`.

The universes `uF` (field) and `uV` (supercuspidal carriers) are independent.
The blocks of `d` have carriers in `max uF uV`, so the inputs are used at
that carrier universe. The isomorphism is an actual isomorphism in the
category of smooth complex representations, not an equality of
Grothendieck-group classes.

## Inputs

All three inputs are published theorems of the Library, not hypotheses:

1. `segmentHeadProductIrreducibility.{uF, max uF uV} F T`
   (module `Classification.SegmentHeadProductIrreducibilityProof`): a
   product of special segment heads is irreducible if and only if its
   multisegment is unlinked.
2. `gelfandKazhdanContragredient.{uF, max uF uV}`
   (module `Smooth.Contragredient.GelfandKazhdanProof`): the smooth
   contragredient of an admissible irreducible representation of `GL_N(F)` is
   its inverse-transpose pullback.
3. The first component of
   `Parabolic.naturalNormalizedInductionDuality.{uF, max uF uV}`
   (module `Parabolic.NaturalInductionDualityProof`): normalized induction
   commutes with smooth contragredients.

It also uses the published lemmas `IsSegmentHead.isAdmissible` and
`IsSegmentHead.isIrreducible` (module `Classification.SegmentHeadProductFiniteness`)
and the reversal theorem `Parabolic.normalizedProductInduced_revPerm_equiv`
of the new helper module `Parabolic.ContragredientReversal` (see
`../Parabolic/ContragredientReversal.md`), which takes inputs 2 and 3 as
hypotheses.

## Proofs

**Pairwise unlinked implies unlinked.** The multisegment is the multiset of
`List.ofFn d.segments`. Membership in it gives indices `i`, `j` with the two
given segments, and the hypothesis at `i`, `j` applies.

**The two-segment theorem.** Fix `n`, a datum `d` with `d.length = 2`, special
heads for both blocks, and unlinked segments `d.segments 0`, `d.segments 1`.
Let `σ = d.shape.adjacentSwap 0`.

1. For two blocks `σ` equals `Fin.revPerm`. Both send `0 ↦ 1` and `1 ↦ 0`;
   the proof is by extensionality, cases on the index value and `omega`.
   The goal is rewritten with this equality.
2. No two segments of `d` are linked. The diagonal cases use
   `Segment.not_isLinked_self`, and the off-diagonal cases use the hypothesis
   and `IsLinked.symm`.
3. The rank is positive, since the segment degrees are positive and sum to
   `n` (`d.degree_sum`). Write `n = m + 1`.
4. Input 1 at `d` and at `d.permute Fin.revPerm` (whose blocks are again
   special heads by `HasSegmentHeads.permute`) gives irreducibility of both
   products, because both multisegments are unlinked by step 2 and
   `multisegment_isUnlinked_of_pairwise`.
5. Each block is admissible by `IsSegmentHead.isAdmissible` and irreducible
   by `IsSegmentHead.isIrreducible`.
6. `PadicField.TopologicalData.SegmentProductDatum.permute_induced` rewrites
   the permuted product as the normalized product of the permuted blocks on
   the permuted shape. `Parabolic.normalizedProductInduced_revPerm_equiv`,
   applied to input 2 (at both universe arguments it requires, here both
   `max uF uV`) and to input 3, then gives a `Representation.Equiv` between
   the two products.
7. `SmoothRep.mkIso` turns this equivalence into the required isomorphism
   `d.induced ≅ (d.permute σ).induced` of smooth representations.

The reversal theorem builds an injective intertwining map between the two
irreducible products: inverse-transpose transport of the product, the
Gelfand–Kazhdan equivalences of the blocks, the canonical tensor-dual map,
induction duality and Gelfand–Kazhdan for the reversed product. Schur's lemma
makes it bijective.

The proof keeps the two given blocks and repeated or equal segments. It uses
no Jordan–Hölder, Grothendieck-group or precedence-order argument. It uses
none of the excluded downstream classification conclusions; the import
closures of the three inputs were checked to contain no proof module of
those tasks.

## Provenance

In Zelevinsky 1980 (*Induced representations of reductive p-adic groups II*,
registered source `zelevinsky-1980-induced-ii`), §9.1, printed p.197, `⟨Δ⟩^t`
is the unique irreducible quotient of the increasing product
`ρ × νρ × ... × ρ'`; this is the special head `IsSegmentHead`. Theorem 9.7(a),
printed p.199, states that `⟨Δ_1⟩^t × ... × ⟨Δ_r⟩^t` is irreducible if and only
if no two of the segments are linked; input 1 is the Library form of this
criterion. The commutation proved here does not follow a printed proof. It is
an internal assembly: irreducibility of both orders together with the
Gelfand–Kazhdan contragredient reversal.
