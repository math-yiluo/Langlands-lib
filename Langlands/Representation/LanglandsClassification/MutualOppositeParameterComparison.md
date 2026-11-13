# Equality of the parameters of two Langlands triplets from mutual cone estimates

Module `Langlands.Representation.LanglandsClassification.MutualOppositeParameterComparison`.

## Purpose and provenance

Derived content for Renard VII.4.2 (ii) (Renard, *Représentations des groupes réductifs
p-adiques*, printed pp.244–246). Renard deduces `M₁ = M₂` and `ℜψ₁ = ℜψ₂` from an
exponent inequality using V.3.18. This module combines the two inequalities supplied by
`exists_weyl_sub_mem_nonnegCone_of_oppositeIntertwining` with the inner-product
comparison of `DominantInvariantFormComparison`. The route differs from Renard's printed
argument.

## Declarations

Fix `(T, i, ν)`, reflection data `D`, and two compatible presentation data
`hⱼ : (⟨T, i, ν, Jⱼ, fⱼ⟩).IsCompatible pⱼ lⱼ aⱼ`. Write `ŷⱼ` for
`leviUnramifiedFullRealPart` of the presentation `⟨⟨T, i, ν, Jⱼ, fⱼ⟩, hⱼ⟩` at `ψⱼ`.

- `pair_leviUnramifiedFullRealPart_nonneg`. If `ℜψ` lies in the open coroot chamber
  `restrictedCorootChamber i ν J f D`, then `ŷ` pairs nonnegatively with every simple
  coroot. The pairing is zero on `J` (`pair_leviUnramifiedFullRealPart_selectedCoroot`)
  and positive off `J` (`pair_leviUnramifiedFullRealPart_pos_of_mem_restrictedCorootChamber`).
- `fullRealPart_eq_and_index_eq_of_mutual_mem_nonnegCone`. Assume both chamber
  conditions and Weyl elements `w₁, w₂` with
  `res_{f₂}(w₁ ŷ₁) − res_{f₂}(ŷ₂) ∈ pres₂.nonnegCone` and
  `res_{f₁}(w₂ ŷ₂) − res_{f₁}(ŷ₁) ∈ pres₁.nonnegCone`. Then `ŷ₁ = ŷ₂` and `J₁ = J₂`.

## Proof

`ŷ₁ = ŷ₂` is `RelativeRootReflectionData.eq_of_mutual_mem_restrictedRootNonnegCone`.
Its hypotheses are: dominance (previous lemma); vanishing on the selected coroots; and
the span condition `ker res_{fⱼ} ⊆ span Jⱼ` (`mem_selectedRootSpan_of_restrict_eq_zero`).
The cone of a presentation is by definition `restrictedRootNonnegCone i ν J f`. Then
`J₁ = J₂` is `selected_eq_of_pair` applied to `y = ŷ₁ = ŷ₂`, which vanishes exactly on
the coroots of `J₁` and of `J₂` among the simple coroots.
