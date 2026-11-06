# Uniqueness of the special-head segment parameter

Author: Worker 1750.

`Langlands.Classification.segmentSpecialParameterUniqueness` proves exactly
the unchanged Library proposition
`Langlands.Classification.SegmentSpecialParameterUniqueness.{uF,uV} F T`
from `SegmentSquareIntegrabilityStatement`. Its telescope is
`{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)`.
The field and representation universes are independent.

The proposition quantifies over actual segments
`Δ Δ' : T.Segment.{max uF uV,uF}`, a degree equality
`h : Δ.degree = Δ'.degree`, and smooth complex representations `π`, `π'`
on the corresponding general linear groups, with carriers in
`Type (max uF uV)`. Given the two strong head relations and an actual
isomorphism `(h ▸ π) ≅ π'`, the theorem proves `Δ = Δ'`.
The target pair and all its imported files are unchanged.

## Implemented proof

The auxiliary theorem `segmentQuotientCuspidalSupport` permits a segment
`Δ : T.Segment.{uV,uF}` with independent base-carrier universe `uV`;
its quotient carrier has universe `max uF uV`. It proves that an actual
irreducible quotient of the increasing segment induction has
`Δ.cuspidalContent` as a supercuspidal support.

Unpacking the quotient relation supplies a supercuspidal representative
`A` of the actual base class, irreducibility of `π`, and a surjective
intertwiner from `T.segmentInduced A.obj Δ.length Δ.rank_pos` to `π`.
For each `i : Fin Δ.length`, set `ρ i = Δ.member i.val` and take `R i`
to be the actual determinant-power twist `ν^i A`, formed with
`SupercuspidalRep.twist`. The existing character properties justify this
supercuspidal twist. The representative equality for `A`, transported
through `T.supercuspidalClassRealPowerTwist`, proves that `R i`
represents `ρ i`.

Each `ρ i` has rank `Δ.rank`, so their rank sum is
`Δ.length * Δ.rank = Δ.degree`. Their `List.ofFn` multiset is
definitionally `Δ.cuspidalContent`. The cuspidal product built from
this family is definitionally the supplied segment induction: its
cuspidal shape has the same constant positive block sizes as
`BlockShape.uniform`, and its representatives give exactly
`T.segmentFactors A.obj Δ.length Δ.rank_pos`. Thus the same
surjective intertwiner, converted with `SmoothRep.ofHom`, gives an
actual quotient of this cuspidal product. The published
`SmoothRep.IsQuotient.isSubquotient` supplies the required subquotient
witness. No segment-head existence theorem is needed.

The main theorem first takes the weak quotient consequence of each supplied
strong head. It applies this auxiliary theorem at segment universe
`max uF uV`. A private equality-transport lemma, proved by equality
elimination on arbitrary ranks, transports the first support to `h ▸ π`.
`IsSupercuspidalSupport.of_iso` then carries it along the supplied
isomorphism to `π'`. Both multisets are now supports of the same actual
irreducible representation. The published theorem
`Langlands.glSupercuspidalSupportUniqueness.{max uF uV,uF}`, with positivity
from `Δ'.degree_pos`, gives
`Δ.cuspidalContent = Δ'.cuspidalContent`.

The membership lemma `Segment.mem_cuspidalContent` converts this equality
into equality of the two segment support sets. Apply the published
`Segment.eq_of_support_eq`, discharging its integral twist freeness
premise with `cuspidalIntegralTwistFreeness F T`. That result recovers
the two endpoints on the same free integral twist line, hence the base
cuspidal datum and the length. Equality of the base datum includes its
positive rank and genuine supercuspidal isomorphism class. The conclusion
is full equality of segments.

## Provenance and dependencies

Henniart 2002, §2.6, printed p.595 (one-based PDF p.9), explicitly states
the bijection `(ρ,m) ↦ St_m(ρ)` and identifies `St_m(ρ)` with the unique
irreducible quotient of the increasing induction. That source page was
read for this contribution:

- Literature ID: `henniart-2002-characterization`.
- SHA256:
  `40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`.
- Retained source:
  `/home/taskhub/central-library/Henniart--Une caracterisation de la correspondance de Langlands locale pour GL(n)--2002.pdf`.

The Lean implementation is an internal derivation from the published
support and twist results, rather than a formalization of a separate
proof printed on that page. Its principal inputs are:

| Published module | Result used |
| --- | --- |
| `Classification.SupercuspidalSupportUniquenessProof` | `Langlands.glSupercuspidalSupportUniqueness`, equality of supports for an actual positive-rank irreducible representation |
| `Classification.SupercuspidalSupport` | Actual cuspidal product and support relations, support invariance under isomorphism, and quotient-to-subquotient conversion |
| `Classification.SegmentCuspidalContent` | Multiset of indexed segment members and `Segment.mem_cuspidalContent` |
| `Classification.SegmentIntegralCoordinates` | `Segment.eq_of_support_eq`, recovery of the full segment from its support under integral twist freeness |
| `Classification.CuspidalIntegralTwistFreenessProof` | `cuspidalIntegralTwistFreeness`, proved nonperiodicity for actual positive-rank cuspidal data |

The existing support uniqueness proof derives association from a common
irreducible subquotient of cuspidal inductions, then compares actual
cuspidal tensors. The freeness proof uses the central character of a
supercuspidal representative and its value at a scalar uniformizer.
Admissibility is already part of those supercuspidal data; it is not an
extra premise imposed on `π` or `π'`.

The recursive project import closure of the five direct imports contains
440 modules. It contains no ordered multisegment head classification
or existence proof, generic segment-product uniqueness proof,
segment-head product irreducibility proof, or essentially square-integrable
classification proof. The main proof uses neither an unproved
classification statement nor an analytic square-integrability argument.
It uses only the quotient part of each supplied head relation and adds
no hypotheses. All external mathematics is reused by published Lean
module and declaration names.

## Validation boundary

The module compiles in the task's prepared environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, with no errors or warnings.
Compilation is development evidence; independent semantic review,
the staged exact-target and Lake validation, and Library publication
are separate acceptance steps.
