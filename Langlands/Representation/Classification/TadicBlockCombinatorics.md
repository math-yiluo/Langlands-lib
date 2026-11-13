# Rectangle decompositions of multisegments

Author: Worker 5121. Module `Langlands.Representation.Classification.TadicBlockCombinatorics`,
namespace `Langlands.Classification.TadicBlockCombinatorics`. Helper module of the proof of
`Langlands.Classification.TadicBlockReductionFromInputs`. Pure multiset and real arithmetic
over the published segment vocabulary, plus the published rigidity of unitary twists.

## Rectangle parameters

`RParam T` records `(ρ, n, d, hd, α)`; `q.rect` is the twisted rectangle
`a(n,d)^(ν^α ρ) = tadicMultisegment (ρ.twist α) n d hd`; `q.Valid` means `ρ` unitary,
`n > 0`, `|α| < 1/2`; `q.refl` replaces `α` by `-α`. `rect_eq` lists the segments
`q.seg j = tadicCenteredSegment ρ d (α + j - (n-1)/2)`, `j < n`;
`tadicCenteredSegment_eq_iff` says centered segments of unitary data agree exactly when the
datum, length and center agree (published `tadicCenteredSegment_twist_eq`).

## Uniqueness of decompositions

`eq_of_sum_rect_eq`: two multisets of admissible parameters with the same sum of rectangles
are equal. Proof by induction on the size: take `q₀` of maximal width `|α| + (n-1)/2`
(`width`). If `α₀ ≥ 0`, its top segment, centered at the width, lies in a rectangle `q` of the
other decomposition; all centers of `q` are bounded in absolute value by the width
(`abs_center_le_width`), which forces the segment to be the top of `q`, `α_q ≥ 0`, and
`α_q + (n_q - 1)/2 = α₀ + (n₀ - 1)/2`; as `|α_q - α₀| < 1/2` this gives `n_q = n₀` and
`α_q = α₀` (`nat_eq_of_real`), so `q = q₀`. The case `α₀ < 0` uses the bottom segment.
Remove `q₀` from both sides and continue (`mem_of_sum_rect_eq_of_maximal`).

## Hermitian reflection

`UnitaryBased Δ`: the beginning of `Δ` is `ν^x ρ` with `ρ` unitary. `reflSeg` sends such a
segment `[ν^x ρ, ν^(x+l-1) ρ]` to `[ν^(-(x+l-1)) ρ, ν^(-x) ρ]` (well defined by the published
`cuspidalDatum_eq_of_twist_eq_of_isUnitary`) and fixes other segments; it is an involution
(`reflSeg_reflSeg`). `map_reflSeg_eq_of_count` converts the count symmetry of
`UnitarizableSocleHermitianSymmetry` into `a.map reflSeg = a`. `rect_refl`: the reflection of
the rectangle of `q` is the rectangle of `q.refl` (segment `j` goes to segment `n - 1 - j`).
`map_refl_eq_of_sum`: if a reflection-invariant multisegment is a sum of admissible
rectangles, the parameter multiset is reflection invariant (uniqueness applied to `J` and
`J.map refl`). `exists_unitary_twist` and `unitaryBased`: every cuspidal datum is a real twist
of a unitary one (published `supercuspidalRepRealUnitarization`, Tadić §2.3).

## Extension and one-element segments

`extSeg Δ = ν^(-1/2)` times `Δ` lengthened by one; `eq_extSeg_dropLast_add`:
`a = ((dropLast a).twist (1/2)).map extSeg + (one-element segments of a)`.
`RParam.ext` lengthens `d` by one and `rect_map_extSeg` gives `a(n,d)^ρ ↦ a(n,d+1)^ρ`.
`stParam ρ n α` is `a(n,1)^(ν^α ρ)`; `stParam_rect_succ_succ`, `stParam_rect_succ_top`,
`stParam_rect_succ_bot` split off end points. `StFamily J`: admissible, `d = 1`,
reflection invariant. `pair_identity`: for unitary `ρ` and `y > 0`, there are such families
`L, R` with `{ν^y ρ, ν^(-y) ρ} + ∑_L rect = ∑_R rect`: if `2y = m + 1` use
`L = a(m,1)^ρ` (omitted for `m = 0`) and `R = a(m+2,1)^ρ`; otherwise, with `m = ⌊2y⌋` and
`α = y - m/2 ∈ (0, 1/2)`, use `R = a(m+1,1)^(ν^{±α} ρ)` and
`L = a(m,1)^(ν^{±(1/2-α)} ρ)` (omitted for `m = 0`). `onePoint_decomposition`: a
reflection-invariant multisegment `φ` of one-element segments satisfies
`φ + ∑_L rect = ∑_R rect` for some families `L, R`, by induction removing a unitary point
`{ρ}` (into `R` as `a(1,1)^ρ`) or a pair `{ν^{±x} ρ}`.

## Source

Tadić 1986 (`tadic-1986-unitary`), Lemma 4.5 (p.358) and the identity on p.361 in the proof
of Lemma 4.8; §2.2–2.4 for the Hermitian involution. The implementation is an independent
combinatorial route.
