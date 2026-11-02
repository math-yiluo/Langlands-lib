# Non-identity shuffle factors occur in every nonzero subrepresentation

Helper module for the juxtaposed case of Zelevinsky 1980, Proposition 4.6
(task 0c90f7e4-78fa-43fd-8736-238bb3e8617d). It contains no statement of its own
from the literature. It formalizes the step of Zelevinsky's argument in which
Frobenius reciprocity shows that each non-identity shuffle tensor `τ_S` is a
quotient of `J(X)` for every nonzero subrepresentation `X` of
`π = ⟨Δ₀⟩ × ⟨Δ₁⟩`.

Notation: `ρ` is a cuspidal datum of rank `r` represented by `A`; `d` is a
two-segment datum whose first segment has base `ν^l ρ` and length `q` and whose
second segment has base `ρ` and length `l`; `π = d.induced`;
`C = BlockShape.uniform (q + l) r`; `J` is the normalized Jacquet functor along `C`;
`τ_S` is the external tensor product of `shuffleFactors F T A.obj (q + l) _ S l 0`
for a set `S ⊆ Fin (q + l)` with `#S = q`.

## Declarations

- `isIrreducible_of_mem_jordanHolderSupport`: a member `τ` of the Jordan–Hölder
  support of `B` is irreducible. Its positive multiplicity counts the graded pieces
  of a simple-factor filtration equivalent to `τ`, so one of them is, and that piece
  is irreducible.
- `exists_ne_zero_jacquet_hom_of_injective`: if `i : π → i_C(σ)` is an injective
  intertwiner and `i_C(σ) ≅ i_C(σ')`, then every nonzero subrepresentation `X` of `π`
  has a nonzero intertwiner `J(X) → ⊗ᵢ σ'ᵢ`. Proof: the composite
  `X ↪ π → i_C(σ) ≅ i_C(σ')` is nonzero because it is injective, and
  `CuspidalSupport.exists_ne_zero_normalizedJacquet_hom` (Frobenius evaluation)
  turns it into a nonzero map on `J(X)`.
- `mem_jordanHolderSupport_jacquetImage`: let `π` be smooth and `τ` a member of the
  Jordan–Hölder support of `J(π)`. If some intertwiner `J(X) → τ` is nonzero, then
  `τ` belongs to the support of the image `jacquetImage T C X` of `J(X)` in `J(π)`.
  Proof: transport the map to the image by `jacquetImageEquiv`, then apply
  `jordanHolderSubobjectSimpleMapDetection` to the inclusion of the image into `J(π)`.
- `exists_ne_zero_jacquet_hom_shuffle`: assume `hswap`: for natural `a, b` with
  `b + 1 < a`, the two orders of the normalized product of `ν^a A` and `ν^b A` on
  `BlockShape.uniform 2 r` are isomorphic. Then for every `S ≠ idShuffle q l` with
  `#S = q` and every nonzero subrepresentation `X` of `π`, there is a nonzero
  intertwiner `J(X) → τ_S`. Proof: `exists_injective_initShuffle` embeds `π` into
  `i_C(τ_{S₀})` with `S₀ = initShuffle q l`; `shuffle_induced_iso` gives
  `i_C(τ_S) ≅ i_C(τ_{S₀})`; apply `exists_ne_zero_jacquet_hom_of_injective`.
- `mem_jordanHolderSupport_jacquetImage_of_ne_id` (cover): assume the statement
  `TwoSegmentSocleShuffleJacquet` and `hswap`. Let `τ` be in the Jordan–Hölder
  support of `J(π)` and not equivalent to `τ_{idShuffle q l}`. Then for every nonzero
  subrepresentation `X` of `π`, `τ` is in the support of the image of `J(X)` in
  `J(π)`. Proof: by the second clause of `TwoSegmentSocleShuffleJacquet`, the
  multiplicity of `τ` in `J(π)` counts the sets `S` with `#S = q` and `τ_S ≃ τ`, so
  such an `S` exists, and `S ≠ idShuffle q l` because `τ` is not equivalent to
  `τ_{idShuffle q l}`. Compose the nonzero map `J(X) → τ_S` of
  `exists_ne_zero_jacquet_hom_shuffle` with `τ_S ≃ τ` and apply
  `mem_jordanHolderSupport_jacquetImage`.
