# Truncating a preceding pair of overlapping segments

Module `Langlands.Representation.Classification.SegmentPrecedenceTruncation`,
namespace `Langlands.PadicField.TopologicalData.Segment`.

This is a helper module for the proof of Zelevinsky, *Induced representations of
reductive p-adic groups II* (1980), Proposition 4.6. In that proof the highest
derivative turns a segment `Δ = [ρ, ν^(m-1) ρ]` into `Δ⁻ = [ρ, ν^(m-2) ρ]`, and a
segment consisting of one cuspidal datum disappears. When `Δ₁` precedes `Δ₂` and the two
overlap, the source uses without comment that `Δ₁⁻` precedes `Δ₂⁻` and that the
union and intersection of the truncated pair are the truncations of the union and
intersection of the original pair. This module states and proves these facts.
The statements are our own (derived) formulation of what the source uses. They
are not quoted from it.

## Truncation

The truncations are the published operations of
`Langlands.Representation.Classification.SegmentInitialTruncation`, which this
module imports; it defines no truncation of its own.

- `Segment.dropLastNonempty Δ h`: for a segment `Δ` of length greater than one
  (`h : 1 < Δ.length`), the segment with the same beginning `Δ.base` and length
  `Δ.length - 1`.
- `Segment.dropLast Δ : Option Segment`: `some (Δ.dropLastNonempty h)` when `Δ`
  has length greater than one, and `none` (the empty segment) when `Δ` is a
  single cuspidal datum. It is evaluated by `dropLast_of_one_lt` and
  `dropLast_of_length_eq_one`.

This module adds one fact about it:

- `HasIntegralCoordinates.dropLastNonempty`: if `Δ` has integral coordinates
  `(a, b)` relative to `ρ`, that is `Δ.base = ν^a ρ` and `b = a + Δ.length - 1`,
  then `Δ.dropLastNonempty h` has coordinates `(a, b - 1)`.

## Symmetry and uniqueness

- `isJuxtaposed_comm Δ Γ`: `Δ.IsJuxtaposed Γ ↔ Γ.IsJuxtaposed Δ`. Linkedness and
  disjointness are both symmetric.
- `IsUnionIntersectionReplacement.symm`: the predicate
  `IsUnionIntersectionReplacement Δ Γ U I` says that `U` has support
  `Δ.support ∪ Γ.support`, and that `I = some J` with `J.support` the
  intersection, or `I = none` and the intersection is empty. It is symmetric in
  `Δ` and `Γ`.
- `IsUnionIntersectionReplacement.unique hfree h₁ h₂`: under integral twist
  freeness of cuspidal data (`Classification.CuspidalIntegralTwistFreeness`),
  two replacements of the same pair agree: `U₁ = U₂` and `I₁ = I₂`. The proof
  uses that a segment is determined by its support (`eq_of_support_eq hfree`).
  A segment always contains its beginning (`base_mem_support`), so an `I = some J`
  cannot coexist with an empty intersection.

## The main lemma

`Precedes.truncation hfree hp hj`: let `A` precede `B` (`hp : A.Precedes B`) and
let them not be juxtaposed (`hj : ¬ A.IsJuxtaposed B`). Then there are proofs
`hA : 1 < A.length`, `hB : 1 < B.length`, segments `U` and `J`, and
`hU : 1 < U.length` such that

1. `IsUnionIntersectionReplacement B A U (some J)`: `U` is the union and `J` the
   (nonempty) intersection of `B` and `A`;
2. `(A.dropLastNonempty hA).Precedes (B.dropLastNonempty hB)`;
3. `IsUnionIntersectionReplacement (B.dropLastNonempty hB) (A.dropLastNonempty hA)
   (U.dropLastNonempty hU) J.dropLast`: the union of the truncated pair is `U⁻`,
   and their intersection is `J⁻`, which is empty (`J.dropLast = none`) when `J`
   is a singleton;
4. `B.rank = A.rank`, `U.rank = A.rank` and `J.rank = A.rank`;
5. `J.support ⊆ U.support`.

Proof. Put `A` in integral coordinates `(0, A.length - 1)` relative to its own
beginning (`hasIntegralCoordinates_self`). Precedence gives coordinates `(c, e)`
of `B` with `0 < c ≤ A.length` and `A.length - 1 < e`
(`of_precedes_right`, `intervalPrecedes_of_precedes`). If `c` were
`A.length`, the supports would be disjoint (`support_inter_eq_empty`), and `A`
would be juxtaposed with `B`. So `c ≤ A.length - 1`, which forces
`A.length ≥ 2`, and `e ≥ c + 1` forces `B.length ≥ 2`. Take
`U = ofIntegralInterval A.base 0 e` and
`J = ofIntegralInterval A.base c (A.length - 1)`. The union and intersection
claims for the original pair are `support_union_eq` and `support_inter_eq`.
After truncation the coordinates are `(0, A.length - 2)` and `(c, e - 1)`.
Precedence of the truncated pair is `precedes_of_intervalPrecedes`. Their union
is `[0, e - 1]`, the coordinates of `U⁻`, and a segment is determined by its
coordinates (`support_eq_iff`). If `J` has length at least two, the
intersection is `[c, A.length - 2]`, the coordinates of `J⁻`. Otherwise
`c = A.length - 1` and the truncated pair is disjoint. The rank equalities come
from `HasIntegralCoordinates.rank_eq`, and `J ⊆ U` from `support_subset_iff`.
