# Segment-socle products inside cuspidal products

Module `Langlands.Representation.Classification.SegmentProductCuspidalEmbedding`,
namespace `Langlands.Classification.SegmentProductCuspidalEmbedding`.

A segment socle `⟨Δ⟩` with `Δ = [ρ, ν^(m-1) ρ]` is an irreducible
subrepresentation of `ρ × νρ × ⋯ × ν^(m-1) ρ`. Hence a product
`⟨Δ_1⟩ × ⋯ × ⟨Δ_r⟩` embeds in the supercuspidal product of all members of all
`Δ_i`, in order. This module records that fact through the predicate
`EmbedsCuspidal T X S`, defined below. The predicate passes to
subrepresentations, isomorphic representations and rank transports. It gives a
supercuspidal support to every irreducible `X`. A nonzero `X` satisfying it has
an irreducible subrepresentation that still satisfies it. The proof of
Zelevinsky's Theorem 6.2 uses this in Case 2 to control the supercuspidal
support of an irreducible subrepresentation of a derivative.

## The predicate

```lean
def EmbedsCuspidal {n : ℕ}
    (X : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (S : Multiset (CuspidalDatum.{uV, uF} T)) : Prop :=
  ∃ (k : ℕ) (ρ : Fin k → CuspidalDatum T) (h : ∑ i, (ρ i).rank = n)
    (A : ∀ i, SupercuspidalRep (n := (ρ i).rank)),
    (∀ i, (ρ i).IsRepresentedBy (A i)) ∧
      (List.ofFn ρ : Multiset _) = S ∧
      ∃ f : X ⟶ T.cuspidalProductInduced ρ h A, Function.Injective (SmoothRep.hom f)
```

(`T.topology` installed.) In words, there are:

- an ordered list `ρ_1, …, ρ_k` of cuspidal data (published `CuspidalDatum`,
  classes of irreducible supercuspidal representations of some `GL_r`), whose
  ranks add up to `n` and whose multiset is `S`;
- actual supercuspidal representatives `A_i` of the `ρ_i`;
- an injective intertwiner from `X` into the actual normalized product
  `A_1 × ⋯ × A_k` (published `cuspidalProductInduced`).

The ordering, the representatives `A_i` and the embedding are all part of the
existential data; only the multiset `S` is fixed.

## Sources and provenance

- Zelevinsky (`zelevinsky-1980-induced-ii`), introduction, printed p.166
  (PDF p.3): `⟨Δ⟩` for `Δ = [ρ, ρ']` "may be defined as the (unique)
  irreducible submodule of `ρ × νρ × ... × ρ'`". This is the published
  `IsSegmentSocle`, used in `embedsCuspidal_induced`.
- Zelevinsky §1.10, printed p.174 (PDF p.11): the support of an irreducible
  `ω` is the multiset `{ρ_1, …, ρ_r}` with `ω ∈ JH(ρ_1 × ⋯ × ρ_r)`. This is the
  published `IsSupercuspidalSupport`, used in `isSupercuspidalSupport`.

`EmbedsCuspidal` itself is an internal derived predicate. It is not a notion
of either source. It packages "is a subrepresentation of a supercuspidal
product with cuspidal multiset `S`". For irreducible `X` it implies
`T.IsSupercuspidalSupport X S`, but it is stronger, since it requires an
embedding and not only a Jordan–Hölder constituent. It is used in the
Case 2 argument of the proof of 6.2 (§6.3 (3), printed p.189, which refers
to the reasoning of §4.5).

## Adapted code and attribution

Two parts of this development reuse published Library code by other workers, who
are coauthors of this submission.

- The member-helper section is now in
  [SegmentProductCuspidalMembers](SegmentProductCuspidalMembers.md), together
  with its attribution to Workers 1070, 328 and 627. This module imports those
  unchanged declarations.
- `normalizedProductInducedMap_injective` is copied from the theorem of the
  same name in `Langlands/Representation/Classification/SegmentEdgeMaps.lean`
  (lines 127–137 at `a9fde216`), by Worker 890. The proof is unchanged. In
  the statement the shape `B` is an explicit argument instead of a section
  variable, and the factor carriers are in `Type (max uF uV)` instead of
  `Type uV`. It is copied rather than imported, which keeps `SegmentEdgeMaps`
  and its imports out of the import closure audited below.

The remaining embedding construction is by Worker 1070.

## Conventions

`{p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}` and `T : F.TopologicalData`
are fixed, with `T.topology` installed. `d : SegmentProductDatum.{uV, uF} T n`
is a published segment-product datum: segments `Δ_j = d.segments j` and blocks
`d.blocks j` on `GL_(deg Δ_j)` with carriers in `Type (max uF uV)`.
`Δ.member i = ν^i Δ.base` is the `i`-th member of `Δ`, and
`Δ.cuspidalContent` is the multiset of its members.
`d.multisegment.cuspidalContent` is the sum of the contents of all segments.

## Declarations

### The members of a segment product

The member refinement, representatives, regrouping isomorphism and multiset
identity are imported from [SegmentProductCuspidalMembers](SegmentProductCuspidalMembers.md).
Their existing namespace, signatures and definitions are unchanged.

### The predicate and its properties

- `EmbedsCuspidal` (definition, the entry declaration): as above.
- `EmbedsCuspidal.of_injective`: if `X` satisfies it and `g : Y ⟶ X` is
  injective, then `Y` satisfies it with the same `S`.
- `EmbedsCuspidal.of_iso`: the same for an isomorphism `Y ≅ X`.
- `EmbedsCuspidal.rankCast`: it passes to the `GL` rank transport along
  `a = b`.
- `normalizedProductInducedMap_injective B f hf`: blockwise injective
  intertwiners induce an injective intertwiner of normalized block products.
  This combines the published `externalMap_injective` and
  `normalizedParabolicInducedMap_injective`.
- `embedsCuspidal_induced d hd`: if every block of `d` is the segment socle of
  its segment (`d.HasSegmentSocles`), then
  `EmbedsCuspidal T d.induced d.multisegment.cuspidalContent`. Proof: choose
  the representatives and socle embeddings `⟨Δ_j⟩ ↪ segmentInduced` provided by
  `IsSegmentSocle`. Induce them blockwise (injective by the previous lemma) and
  compose with `memberInducedIso`.
- `EmbedsCuspidal.isSupercuspidalSupport hX hirr`: if `X` is irreducible and
  satisfies `EmbedsCuspidal T X S`, then `T.IsSupercuspidalSupport X S`
  (published `IsCuspidalSubrepresentation.isCuspidalConstituent`).
- `EmbedsCuspidal.exists_irreducible hn hX`: let `0 < n`, let `X` be
  nontrivial, and let `X` satisfy `EmbedsCuspidal T X S`. Then some
  irreducible subrepresentation `σ` of `X`
  (`IsIrreducibleSubrepresentation X.representation σ.representation`)
  satisfies `EmbedsCuspidal T σ S`. Proof: the supercuspidal product has finite
  length (published `irreducibleProductFiniteLength`), hence so does `X`.
  Its subrepresentation lattice is therefore atomic. An atom is irreducible
  (`FiniteIndexRestriction.isIrreducible_toRepresentation_of_isAtom`) and
  embeds in `X`.

## Import audit

This module is submitted together with `SegmentProductSplit` and
`SegmentContentShift` (both in `Langlands.Representation.Classification`).
On Library base `2d873b3c` (as on the earlier bases `7114a390`, `a9fde216`
and `6cb15022`), the
transitive project import closure of these
three modules has 525 modules: the three themselves and 522 published
Library modules. The one published proposition taken as an explicit
hypothesis is the integral twist freeness statement
`CuspidalIntegralTwistFreeness` (`hfree` in `SegmentContentShift`). Its
published proof module `CuspidalIntegralTwistFreenessProof` is not imported.
The published proved results used directly are `irreducibleProductFiniteLength`
(`IrreducibleProductFiniteLengthProof`), `orderedProductRegrouping`
(`OrderedProductRegroupingProof`) and `headTailProductInductionIso`
(`HeadTailProductInduction`). The closure also contains other published
proofs, for example the supercuspidal-support and Jacquet-module proofs
below these modules. The closure contains no module for the conclusions excluded by task `b711af72`
(segment-socle irreducibility, swaps or commutation, exhaustion,
special-head, tempered-block or square-integrable classification, or generic
uniqueness). It also contains no two-supercuspidal product module.
