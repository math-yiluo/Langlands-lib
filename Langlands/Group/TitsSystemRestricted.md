# Saturation, parabolic subgroups and the restricted building of a Tits system

This module adds the Tits-system notions that KP Axiom 4.1.9 uses to the Library
interface `Langlands.Group.TitsSystem`. That interface has the Tits-system predicate
`Langlands.Group.IsTitsSystem B N π S`, the Bruhat cells `TitsSystem.cell` and the
standard parabolic subsets `TitsSystem.standardParabolic B π X = B W_X B`. Axiom 4.1.9
(as corrected) asks for three things. The Iwahori–Tits system must be *saturated*.
Facet stabilizers must be *parabolic subgroups* of it. Its associated *restricted
building* must be the building of Axiom 4.1.1. This module states these notions for
subgroups `B`, `N` of an arbitrary group `G`, with a Weyl-group datum `π : N →* W` and
a set `S ⊆ W`. It contains definitions and two unfolding lemmas only. No property of
Tits systems is assumed or proved, and nothing requires `(B, N, π, S)` to be a Tits
system.

Source: T. Kaletha and G. Prasad, *Bruhat–Tits theory: a new approach* (2023),
registered as `kaletha-prasad-2023-bruhat-tits-new-approach`. Page numbers are PDF
pages of that file, with the printed page in parentheses. The 2024 corrections
(`kaletha-prasad-2024-corrections`) change nothing in §§1.4–1.5 that this module uses.

## Definitions

| Lean declaration | Source | Content |
|---|---|---|
| `TitsSystem.IsSaturated B N` | KP Definition 1.4.1, axiom TS 5, PDF 78 (p. 47) | `⨅ n : N, n B n⁻¹ = B ⊓ N`, written as the infimum over `n ∈ N` of the images of `B` under conjugation by `n`. |
| `TitsSystem.IsParabolic B P` | KP Definition 1.4.4(2), PDF 79 (p. 48) | `P` contains a conjugate `g B g⁻¹` of `B`. |
| `TitsSystem.conjStandardParabolic B π g X` | KP Definitions 1.4.4(1) and 1.4.6, PDF 79 (p. 48) | The subset `g G_X g⁻¹` of `G`, where `G_X = B W_X B` is the Library's `standardParabolic B π X`. A parabolic subgroup has type `X` when it equals such a conjugate. |
| `TitsSystem.SameComponent S` | KP §1.4 after Definition 1.4.6, PDF 79 (p. 48) | The reflexive–transitive closure of the relation "`s, t ∈ S` and `st ≠ ts`". Its classes on `S` are the parts `S₁, …, Sₙ` of the smallest decomposition of `S` into mutually commuting parts, the irreducible components. |
| `TitsSystem.IsAdmissibleType S X` | KP Definition 1.5.17(1), PDF 92 (p. 61) | `X ⊆ S`, and each `s ∈ S` has an element `t` of its component with `t ∉ X`. So `X ∩ Sᵢ` is a proper subset of every component `Sᵢ`. |
| `TitsSystem.IsAdmissibleParabolic B π S P` | KP Definition 1.5.17(2), PDF 93 (p. 62) | `P` equals `g G_X g⁻¹` (as a set) for some `g ∈ G` and an admissible `X`, so its type is admissible. |
| `TitsSystem.restrictedApartment B π S g` | KP Proposition 1.5.6(6), PDF 87 (p. 56); Remark 1.5.7, PDF 89–90 (pp. 58–59); Proposition 1.5.18(1), PDF 93 (p. 62) | The set of subgroups `P` with `P = (g n) G_X (g n)⁻¹` for some `n ∈ N` and admissible `X`. This is the apartment `g A' = g (B' ∩ A)` of the restricted building, in the parabolic-subgroup description. |
| `TitsSystem.restrictedApartments B π S` | KP Proposition 1.5.18(1) and Definition 1.5.20, PDF 93 (p. 62) | The range of `g ↦ restrictedApartment B π S g`: the set of all apartments of the restricted building. |

Lemmas: `isSaturated_iff` and `mem_restrictedApartment` unfold the definitions.
`isAdmissibleParabolic_of_mem_restrictedApartment` shows that every member of a
restricted apartment is an admissible parabolic subset.

## How the definitions match the source

*Parabolic description of the building.* KP Proposition 1.5.6(2) gives a
`G`-equivariant bijection `F ↦ P_F` between the facets of the Tits building and the
proper parabolic subgroups. It reverses the face relation. Remark 1.5.7 then reads the
building as the set of parabolic subgroups, ordered by opposite inclusion. In this
description the standard apartment `A` (the `N`-conjugates of the faces of the standard
chamber) consists of the subgroups `n G_X n⁻¹` with `n ∈ N` and `X ⊊ S`. The apartments
are the translates `g A`. By Proposition 1.5.18(1) the restricted building `B'` consists
of the admissible facets, and its apartments are the sets `B' ∩ g A`. A facet is
admissible when the type `X` of its parabolic subgroup is admissible (Definition
1.5.17). This gives `restrictedApartment`. When `S` is nonempty, every admissible `X`
is a proper subset of `S`, so these subgroups are proper parabolic subgroups.

*Types.* Definition 1.4.6 defines the type of a parabolic subgroup `P` as the unique
`X ⊆ S` with `P` conjugate to `G_X`. Uniqueness is Proposition 1.4.5(2), which this
module does not prove. `IsAdmissibleParabolic` therefore asks that *some* conjugate
`g G_X g⁻¹` with admissible `X` equals `P`. In a Tits system this is the source notion.

*Subsets and subgroups.* The Library defines `standardParabolic` as a subset of `G`.
That it is a subgroup when `X ⊆ S` is part of the abstract theory and is not assumed.
Here, subgroups `P` are compared with these subsets through their carriers,
`(P : Set G) = conjStandardParabolic B π g X`.

*Irreducible components.* KP writes `S = S₁ ∪ ⋯ ∪ Sₙ` for the unique smallest
decomposition into parts whose elements commute across different parts. For `s, t ∈ S`,
they lie in the same part exactly when a chain of elements of `S` joins them with
consecutive elements not commuting. `SameComponent` is this chain relation. KP's
standing hypothesis "`S` finite and non-empty" (Definition 1.5.17, Proposition 1.5.18)
is not built into the definitions. Axiom 4.1.9 states it as a separate clause.

## Use

Axiom 4.1.9 (KP PDF 192, p. 161, with the corrections of
`kaletha-prasad-2024-corrections` PDF 27) is assembled in a later unit of task
`129deca1-ce21-411b-9b79-7e94545fe26d`. That unit applies these definitions to the
Iwahori subgroup and the normalizer intersected with `G(F)^0`, with
`Langlands.Group.IsTitsSystem`. The corrected wording "facet stabilizers are *a*
parabolic subgroup" is the predicate `IsParabolic`. The identification of the
restricted building with the building of Axiom 4.1.1 compares the facets of
`B(G)` with admissible parabolic subgroups, and the apartments with
`restrictedApartments`.
