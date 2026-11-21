# Conjugation and isomorphism of pairs `(J, λ)`

Source: C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993), Theorem (5.7.1), printed p. 195 (PDF p. 207), where two simple types `(J₁, λ₁)`, `(J₂, λ₂)` are shown to satisfy `J₂ = x⁻¹J₁x` and `λ₂ ≅ λ₁^x` for some `x ∈ G`, with `λ₁^x(h) = λ₁(x h x⁻¹)` as in (5.1.7), printed p. 160. This is definition 6 of Task 7427, which spells out the convention as a left action: `g·(J, λ) = (gJg⁻¹, λ^{g⁻¹})` with `λ^{g⁻¹}(gjg⁻¹) = λ(j)`. With `g = x⁻¹`, `g·(J₁, λ₁) = (x⁻¹J₁x, λ₁^x)`, so the two formulations describe the same relation.

A pair is a subgroup `J` of a group `G` together with a representation `ρ : Representation ℂ J W` on a complex vector space `W`. The definitions make sense for any group `G`; in Task 7427, `G = Aut_F(V)` and `J` is compact open.

## Definitions

- `Langlands.Group.RelativeWeyl.conjugateSubgroup g J` is the subgroup `gJg⁻¹`, the image of `J` under `y ↦ g y g⁻¹` (`mem_conjSubgroup`).
- `conjSubgroupEquiv g J : J ≃* gJg⁻¹` is `j ↦ g j g⁻¹`.
- `conjRepresentation g ρ` is the representation `λ^{g⁻¹}` of `gJg⁻¹` defined by `λ^{g⁻¹}(gjg⁻¹) = ρ(j)`, that is, `ρ` composed with the inverse of `conjSubgroupEquiv g J`. The lemma `conjRepresentation_conjSubgroupEquiv` records this formula.
- `IsPairIsomorphic ρ₁ ρ₂`, for `ρ₁` a representation of `J₁` and `ρ₂` of `J₂`: the subgroups are equal, `h : J₁ = J₂`, and `ρ₁`, transported to `J₂` along `h`, is isomorphic to `ρ₂` as a representation of `J₂` (`Representation.Equiv`, a `ℂ`-linear isomorphism commuting with the actions). The carriers `W₁`, `W₂` may be different types, in different universes.
- `AreConjugatePairs ρ₁ ρ₂`: the pairs are `G`-conjugate, that is, `IsPairIsomorphic (conjRepresentation g ρ₁) ρ₂` for some `g ∈ G`. In words, `(J₂, ρ₂)` is isomorphic to `g·(J₁, ρ₁)`.

The conjugation convention is a left action: `g·(h·(J, λ))` is isomorphic to `(gh)·(J, λ)`. This module does not prove that, nor that `AreConjugatePairs` is an equivalence relation; these are not needed to state the definitions.
