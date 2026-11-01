# Shifted cuspidal contents of segments

Module `Langlands.Representation.Classification.SegmentContentShift`,
namespace `Langlands.Classification.SegmentContentShift`.

This module does the multiset bookkeeping for Case 2 of Zelevinsky's proof of
Theorem 6.2. For a segment `Δ = [ρ, ν^(m-1) ρ]`, write `Δ⁻ = [ρ, ν^(m-2) ρ]`
(absent when `m = 1`), `b(Δ) = ρ` for its beginning and `e(Δ) = ν^(m-1) ρ`
for its end. The main result, `not_map_twist_le`, says the following. Assume
that no nonzero integral power of `ν` fixes a cuspidal datum, and that no
later segment begins at `ν · e(Δ_1)`. Then

`ν · (Δ_1 + Δ_2⁻ + ⋯ + Δ_r⁻) ≰ Δ_1 + Δ_2 + ⋯ + Δ_r`

as multisets of cuspidal data. In words, the support of
`⟨Δ_1⟩ × ⟨Δ_2⁻⟩ × ⋯ × ⟨Δ_r⁻⟩`, shifted by `ν`, is not contained in the support
of `⟨Δ_1⟩ × ⋯ × ⟨Δ_r⟩`.

## Provenance

This is internal derived material. Zelevinsky (`zelevinsky-1980-induced-ii`,
§6.3 (3), printed p.189, PDF p.26) says that in Case 2 "one has to use the
reasoning of 4.5 which leads to the equality `ρ_i ≃ νρ_1'`. This
contradicts the assumptions of 6.2." Here `ρ_i` is the beginning of some
`Δ_i` and `ρ_1'` the end of `Δ_1`. The assumption of 6.2 is that `Δ_1` is
followed by no segment beginning at `ν e(Δ_1)`. That assumption appears in
`not_map_twist_le` as `hsep` for the later segments. For `Δ_1` itself the
equality `b(Δ_1) = ν e(Δ_1)` is excluded by integral twist freeness: the
published proposition `Classification.CuspidalIntegralTwistFreeness F T`,
taken here as an **explicit hypothesis `hfree`**. It has a published proof,
`CuspidalIntegralTwistFreenessProof`, which this module does not import. The
lemmas below are the exact multiset form of "leads to the equality".

## Conventions

`{p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}`.
`T.Segment` and `T.CuspidalDatum` are the published types.
`Δ.cuspidalContent` is the multiset `{Δ.member i | i < Δ.length}`, where
`Δ.member i = Δ.base.twist i`, and `Δ.last = Δ.member (Δ.length - 1)`.
`CuspidalDatum.twist 1` is the twist by `ν = |det|`, written `ν ·` below.

## Declarations

- `lower Δ` (definition): `Δ⁻` as an `Option`. It is `some` of the segment
  with the same beginning and length `Δ.length - 1` when `2 ≤ Δ.length`, and
  `none` otherwise.
- `lower_content Δ h`: for `2 ≤ Δ.length`, `ν · Δ⁻ + {b(Δ)} = Δ`.
- `content_map_twist_add_base Δ`: `ν · Δ + {b(Δ)} = Δ + {ν · e(Δ)}`.
- `filterMap_lower_content L`: for a list `L` of segments,
  `ν · (∑_{Δ ∈ L, |Δ| ≥ 2} Δ⁻) + {b(Δ) | Δ ∈ L} = ∑_{Δ ∈ L} Δ`. Singletons
  contribute `{b(Δ)} = Δ` on both sides.
- `exists_base_eq_last_twist Δ₁ L h`: if
  `ν · (Δ₁ + ∑_{Δ ∈ L} Δ⁻) ≤ Δ₁ + ∑_{Δ ∈ L} Δ`, then some `Δ ∈ Δ₁ :: L` has
  `b(Δ) = ν · e(Δ₁)`. Proof: adding the beginnings of all segments of
  `Δ₁ :: L` to the left side gives `Δ₁ + ∑_L Δ + {ν · e(Δ₁)}`, by the two
  previous identities. So `{ν · e(Δ₁)}` is at most the multiset of beginnings.
- `base_ne_last_twist hfree Δ`: under `hfree`, `b(Δ) ≠ ν · e(Δ)`. Indeed
  `ν · e(Δ) = ν^(Δ.length) · b(Δ)` with `Δ.length > 0`.
- `not_map_twist_le hfree Δ₁ L hsep`: assume `hfree`, and assume
  `hsep : ∀ Δ ∈ L, b(Δ) ≠ ν · e(Δ₁)`. Then
  `¬ ν · (Δ₁ + ∑_{Δ ∈ L} Δ⁻) ≤ Δ₁ + ∑_{Δ ∈ L} Δ`. This combines the two
  previous results.
