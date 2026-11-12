# Renard VI.4.4, Lemma: the groups T ⊂ H ⊂ N and restriction to T

Author: Worker 1222. Module
`Langlands.Representation.CuspidalSupport.RationalSummandStabilizerLemmaStatement`,
namespace `Langlands.CuspidalSupport`. Statement
`RationalSummandStabilizerLemmaStatement : Prop` (universe parameters `uF`, `uV`); nothing is
proved here.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, VI.4.4: the preliminary remarks, (VI.4.4.1)–(VI.4.4.2) and the definition of `T`,
printed pp.155–157 / PDF pp.161–163; the Lemma and its proof, printed pp.157–158 / PDF
pp.163–164. The registered source ID is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

Setting (VI.4.1–VI.4.4): `(π, V)` is an irreducible supercuspidal representation of `G`,
`(ρ, W)` an irreducible summand of `Res_{⁰G}^G π`, with `W ⊂ V` a `⁰G`-stable subspace, and
`N = N_G(ρ)` the stabilizer of `ρ` in `G`. Renard sets

`H = {g ∈ G | π(g)·W = W}`,

lets `ρ_H` be the representation of `H` on `W` given by `π`, and introduces
`H̃ = {g ∈ G | ρ_H^g ≃ ρ_H}`, the normalizer of `ρ_H`. Replacing `W` by another copy of `ρ`
finitely many times, "one may finally assume that `W` was chosen so that `H = H̃`". With
`X(G)(π) = {ω ∈ X(G) | π ⊗ ω ≃ π}`, he sets `T = ⋂_{ω ∈ X(G)(π)} ker ω`. Let `m` be the
multiplicity of `ρ` in `Res_{⁰G}^G π`.

**Lemma.** `T ⊂ H ⊂ N` with `[N : H] = [H : T] = m`. Let `ρ_T` be the restriction of `ρ_H`
to `T`. Then every irreducible component of `Res_T^G(π)` whose restriction to `⁰G` contains
`ρ` is isomorphic to `ρ_T`. The restriction morphism

`Hom_T(ρ_T, Res_T^G(π)) → Hom_{⁰G}(ρ, Res_{⁰G}^G(π))` (VI.4.4.3)

is an isomorphism.

The published `RationalSummandEndCenterStatement` (the Theorem of VI.4.4) records that it does
not state this Lemma. This module states it.

## Setting in Lean

The binders, up to and including `π` and `ρ`, are exactly those of the published
`RationalSummandEndCenterStatement` (same namespace), whose Markdown describes them: an
arbitrary connected reductive `G` over an arbitrary nonarchimedean local field `F`, a maximal
split torus `i : S → G`, a generic cocharacter `ν`, the premises `StandardCocharacterStatement`,
`HasRelativeRootSystem i` and closedness of the standard unipotent radicals; local
compactness, the nonarchimedean property and Hausdorffness of `G(F)` with its canonical
topology; `π` an irreducible smooth complex representation of `G(F)` with carrier in
`Type uV`, cuspidal in the sense of `Aubert.General.IsCuspidal`; `ρ` an irreducible smooth
representation of `⁰G = rationalCommonNormKernel G` with carrier in `Type uV`. In place of a
given embedding, the statement assumes that some injective `⁰G`-map
`ρ → Res := SmoothRep.restrictSubgroup (rationalCommonNormKernel G) π` exists, that is, `ρ`
occurs in the restriction of `π`. `T` is the subgroup of the Theorem's statement: the
infimum of the kernels of the unramified characters `ω` with `π ⊗ ω ≅ π`.

## Statement

A map `j : ρ ⟶ Res` plays the role of `W`: `W` is its image. The statement uses these
predicates on `g ∈ G(F)`:

- `InN g`: there is a `ℂ`-linear bijection `A : ρ ≃ ρ` with
  `A(ρ(y) w) = ρ(x) A(w)` whenever `x, y ∈ ⁰G` and `y = g⁻¹ x g`. This says `ρ^g ≅ ρ`, with
  `ρ^g(x) = ρ(g⁻¹ x g)`, Renard's convention (`π(g)` intertwines `ρ^g` on `W` with `π` on
  `π(g)·W`). So `N = {g | InN g}` is Renard's `N_G(ρ)`.
- `InH j g`: for every `v ∈ V`, `v ∈ W ↔ π(g) v ∈ W`. Since `π(g)` is invertible this is
  `π(g)·W = W`, so `{g | InH j g}` is Renard's `H`.
- `InHtilde j g`: there is a `ℂ`-linear bijection `A : ρ ≃ ρ` such that
  `π(k)(j(A w)) = j(A w')` whenever `k` satisfies `InH j k` and `j(w') = π(g⁻¹ k g)(j w)`.
  Through `j`, `ρ_H(k)` is the operator `w ↦ w'` with `j(w') = π(k)(j w)`, so this says that
  `A ∘ ρ_H(g⁻¹ k g) = ρ_H(k) ∘ A` for `k ∈ H`, that is, `ρ_H^g ≅ ρ_H`. So
  `{g | InHtilde j g}` is Renard's `H̃`.
- `Good j`: `j` is injective and every `g` with `InHtilde j g` satisfies `InH j g`. Since
  `H ⊂ H̃` always holds (`ρ_H(h)` intertwines `ρ_H^h` and `ρ_H`), this is Renard's choice
  `H = H̃`.
- `TStable E`, for a subspace `E` of the carrier of `π`: `π(t) v ∈ E` for `t ∈ T`, `v ∈ E`.

The statement asserts:

1. a good `j` exists;
2. for every good `j` there are `m : ℕ` and subgroups `H`, `N` of `G(F)` with
   - `Module.rank ℂ (ρ ⟶ Res) = m`;
   - `g ∈ H ↔ InH j g` and `g ∈ N ↔ InN g` for all `g`;
   - `T ≤ H`, `H ≤ N`, `H.relIndex N = m` and `T.relIndex H = m`. Mathlib's
     `A.relIndex B` is the index of `A ⊓ B` in `B`, so these are `[N : H] = m` and
     `[H : T] = m`;
   - (VI.4.4.3) for every `ψ : ρ ⟶ Res`, every `t ∈ T` and all `w, w'` with
     `j(w') = π(t)(j w)`: `ψ(w') = π(t)(ψ w)`;
   - for every subspace `E` of the carrier of `π` that is `T`-stable, nonzero and has no
     `T`-stable subspaces other than `⊥` and `E`, and that contains the image of some nonzero
     `ψ : ρ ⟶ Res`, there is a `ℂ`-linear bijection `A : ρ ≃ E` with `A(w') = π(t)(A w)`
     whenever `t ∈ T` and `j(w') = π(t)(j w)`.

## Correspondence

- **`m`.** Renard's `m` is the multiplicity of `ρ` in `Res_{⁰G}^G π`. As in the published
  Theorem statement, `m` is taken to be `dim Hom_{⁰G}(ρ, Res π)`, which by Schur's lemma for
  `ρ` is the number of summands isomorphic to `ρ`; finiteness is part of the conclusion.
- **`ρ_T` and (VI.4.4.3).** Renard's `ρ_T` acts on `W`; through `j` it acts on the carrier of
  `ρ` by `ρ_T(t) w = w'` with `j(w') = π(t)(j w)`. A `T`-map `ρ_T → Res_T π` is a linear map
  `ρ → V` that is `T`-equivariant in this sense. It restricts to a `⁰G`-map with the same
  underlying linear map, because `ρ_T` restricted to `⁰G` is `ρ`. The restriction map
  (VI.4.4.3) is therefore always injective, and it is surjective exactly when every
  `⁰G`-map `ψ : ρ → Res π` is `T`-equivariant. The fourth item asserts this.
- **Components.** Renard treats `Res_T^G π` as a direct sum of irreducible components, as
  for `⁰G` in VI.3.2 (`T` contains `⁰G` and has finite index in `G`). Its irreducible
  components are read as its irreducible subrepresentations, the `T`-stable subspaces `E`
  described in the last item. "Its
  restriction to `⁰G` contains `ρ`" is the existence of a nonzero `⁰G`-map `ρ → E`, written as
  a nonzero `ψ : ρ ⟶ Res` with image in `E`. "Isomorphic to `ρ_T`" is a `T`-equivariant linear
  bijection `ρ → E`, with `ρ_T` read through `j` as above.
- **The choice of `W`.** Renard proves the Lemma for the `W` chosen with `H = H̃`. The
  statement quantifies over all good `j`, so it covers every such choice, and the first
  clause asserts that one exists, which is the source's "on peut supposer finalement".
- **Subgroups.** `H` and `N` are given as subgroups characterized by their membership
  predicates. They are unique, and the conclusion asserts that the predicates define
  subgroups. Renard's proof uses that `H` is normal in `G`; the statement does not assert
  this.

## Faithfulness notes

- The setting is that of the published `RationalSummandEndCenterStatement`, and its notes on
  cuspidality (vanishing of the proper standard normalized Jacquet modules, for Renard's
  supercuspidal), universes and the absence of splitness, characteristic or admissibility
  premises apply unchanged.
- The statement does not assert that `X(G)(π)` is finite or that `T` has finite index; these
  are used in the proof.
- The second assertion of the Lemma (components) follows from the third and irreducibility
  of `ρ`; both are stated because the source states both.

## Remaining obligations

The proof is a separate obligation. The source proof uses the preliminary remarks of VI.4.4
(the decomposition (VI.4.4.2), `π ≃ ind_H^G(ρ_H)`, `[N : H] = m`, and the replacement argument
giving a `W` with `H = H̃`), Proposition VI.3.2 (iii) adapted to `T` and `H`, the duality
between tori and lattices for `X(G)`, and the adjunction (VI.4.4.4) together with
`ind_T^H ρ_T ≃ ⊕_ξ ρ_H ⊗ ξ` to compute `[H : T] = m`. None of this is asserted here.

## Provenance

Source assertion: the Lemma of Renard 2026 VI.4.4, with the objects `H`, `H̃`, `N`, `T`, `ρ_H`,
`ρ_T` of the preliminary remarks. Formal choices: the setting of the published Theorem of
VI.4.4; `W` as the image of an injective `⁰G`-map; `H`, `H̃`, `N` through membership
predicates read on the carrier of `ρ`; Renard's choice `H = H̃` as the condition `H̃ ⊆ H`,
with existence of such a choice asserted; (VI.4.4.3) as `T`-equivariance of every
`⁰G`-map; components as irreducible `T`-stable subspaces.
