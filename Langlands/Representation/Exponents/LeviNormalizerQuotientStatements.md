# The group `W(A) = N_G(M)/M` of a rational Levi: finiteness and faithfulness

Author: Worker 1697. This module states two structural facts about the normalizer of a
rational Levi subgroup. The proof of Renard's VI.8.5 uses both. Nothing is proved here.

## Source

Renard, *Représentations des groupes réductifs p-adiques*, French version of 9 July 2026
(`renard-2026-representations-groupes-reductifs-padiques`):

- V.3.5 (printed pp.110–111, PDF pp.116–117). For a parabolic `P = MN` with split
  component `A`, the Weyl group `W(A) = N_G(A)/Z_G(A) = N_G(A)/M = N_G(M)/M` (V.3.5.1)
  acts on `X^*(A)`, hence on `X_*(A) ≃ Λ(A)`, `𝔞^*` and `𝔞`. "L'action de `W(A)` sur
  `X^*(A)` ou sur `X_*(A) ≃ Λ(A)` est fidèle."
- V.4.3 (printed p.119, PDF p.125), (V.4.3.3): `W(M, M)/W_M ≃ W(A)`. Here
  `W(M, M) ⊂ W_G` and `W_G` is the finite Weyl group of the relative root system
  (V.3.7, printed p.111, PDF p.117). So `W(A)` is finite.
- V.3.19 (printed p.115, PDF p.121): `X_*(A) ⊂ Λ(M) ⊂ X_*(M)` are lattices of the same
  rank.
- VI.8.5, proof (printed p.194, PDF p.200) uses that `W(M, M)/W_M ≃ W(A)` (V.4.3.3)
  "agit fidèlement sur `𝔞^*` (V.3.5)". It also uses the finite index `w ∈ W(M, M)/W_M`
  of the VI.5.3(iii) filtration.

Renard writes `G` for the group of rational points. So `N_G(M)/M` is the quotient of
groups of `F`-points.

## Setting and conventions

Both statements quantify over a nonarchimedean local field `k`, a connected reductive
group `G` over `k`, and actual group schemes `P`, `M` with morphisms `p : P ⟶ G` and
`l : M ⟶ P`, where `IsParabolicSubgroup p` and `IsRationalLeviSubgroup l` hold.
`rationalPoints G` is `G(k)`. `pointImage (l ≫ p)` is the image of `M(k)` in `G(k)`.

An element `w ∈ G(k)` *normalizes* `M` when an isomorphism `φ : M ≅ M` satisfies
`φ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso w).hom`. This is an equality of morphisms of group
schemes, so the closed subgroup `M` of `G` is stable under `Int(w)` and `φ` is the
induced automorphism. Such a `φ` is unique because `l ≫ p` is a monomorphism. On
rational points, `rationalPoints.map φ.hom` is `m ↦ w m w⁻¹` read in `M(k)`.

## `LeviNormalizerFiniteQuotientStatement` (V.4.3.3)

There are `n : ℕ` and `g : Fin n → G(k)` such that

- every `g j` normalizes `M` (for some `φ : M ≅ M`);
- every `w ∈ G(k)` that normalizes `M` (through some `φ`) has the form
  `w = g j * p(l(m))` for some `j` and some `m ∈ M(k)`.

So the `g j` meet every coset of `M(k)` in `N_G(M)(k)`, and `N_G(M)(k)/M(k)` is finite.
This is the finiteness of `W(A) = N_G(M)/M`, obtained from (V.4.3.3) and the finiteness
of `W_G`. The statement does not require the `g j` to lie in distinct cosets.

## `LeviNormalizerNormFixingStatement` (V.3.5)

Let `w ∈ G(k)` normalize `M` through `φ`. Suppose that for every `a` in the centre
`Subgroup.center (rationalPoints M)` of the abstract group `M(k)` and every rational
character `χ` of `M`,

`(rationalNormCharacters M χ).toMul (rationalPoints.map φ.hom a) = (rationalNormCharacters M χ).toMul a`,

that is, `‖χ(φ(a))‖ = ‖χ(a)‖` for the normalized absolute value of `k`. Then
`w ∈ pointImage (l ≫ p)`, that is, `w ∈ M(k)`.

This is the faithfulness in V.3.5, transported from `Λ(A)` to norms on the centre. The
points `A(k)` of the split component are central in `M(k)`, and `φ` preserves `A`.
The norms `‖χ(a)‖`, for `χ ∈ X^*(M)`, determine the image of `a ∈ A(k)` in
`Λ(M) ⊗ ℝ`. Since `Λ(A) ⊂ Λ(M)` have the same rank (V.3.19), the hypothesis says that
the class of `w` in `W(A)` acts trivially on `Λ(A) ≃ X_*(A)`. Faithfulness then makes
that class trivial, so `w ∈ M`. The hypothesis covers the whole centre of `M(k)`, not
only `A(k)`. That makes it stronger than what faithfulness needs, so the statement is a
consequence of the source.

## `LeviNormalizerWeylGroupStatements`

The conjunction of the two statements, at the same universe `u`.

## Use

`genericInducedIrreducibility_of_inputs` (Renard VI.8.5 from its inputs) uses both
statements. The VI.5.3(iii) filtration of `r_P^G i_P^G (ρ ⊗ ψ)` chooses its
double-coset representatives `z_i` only after the twist `ψ` is fixed. The finiteness
statement replaces them by the fixed `g j`. On the centre of `M(k)`, `Int(z_i)` and
`Int(g_j)` agree when `z_i ∈ g_j M(k)`. The faithfulness statement then gives, for each
`g j ∉ M(k)`, a central point whose norms `g j` moves. This yields one hypersurface in
`X(M)` to avoid for each `j`.
