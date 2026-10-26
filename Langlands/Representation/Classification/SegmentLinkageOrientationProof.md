# Proof of orientation of linked segments

`Langlands.Classification.segmentLinkageOrientation` proves the internal
proposition `Langlands.Classification.SegmentLinkageOrientation`. Its outer
parameters are a prime `p`, a p-adic field `F`, and topology datum `T`, with
independent field and representation universes. It asserts that for every
`Δ Γ : T.Segment`, linkage implies `Δ.Precedes Γ ∨ Γ.Precedes Δ`.

The private helper `support_subset_of_base_eq_length_le` shows that equal
bases and a length inequality give support containment: a member of the
shorter segment has the same natural twist index in the longer segment.
For a linked pair, either ordering of their lengths would contradict one
of the two support noncontainments if their bases were equal. Their bases
are therefore distinct.

The segment witnessing the support union contains both bases. Choose
natural indices `a` and `b` representing those bases in that segment.
Equality of these indices would imply equality of the bases, so `a ≠ b`.
If `a < b`, the positive natural difference `b - a` supplies the shift for
`Δ.Precedes Γ`. Rewriting the bases using their indices,
`CuspidalDatum.twist_twist` and `Nat.cast_sub` reduce the required equality
to real arithmetic, which `ring` proves. If `b < a`, the same argument
with `a - b` and `IsLinked.symm` gives `Γ.Precedes Δ`.

The public helper
`Langlands.PadicField.TopologicalData.Segment.IsLinked.precedes_or_precedes`
implements this argument. The closing theorem applies it to the universally
quantified published proposition. The proof is derived from the existing
support, linkage, precedence, and twist definitions in `Segments`.
Worker 346 authored the reused Lean proof; Worker 328 checked it against
the published statement and prepared this proof documentation.

The conclusion asserts at least one direction of precedence, without
asserting exclusivity or uniqueness of the shift. The proof uses neither
injectivity of twisting nor uniqueness of the chosen indices, and introduces
no analytic or classification assumptions. It establishes no exponent
comparison, square-integrable nonlinkage, or tempered classification result.
