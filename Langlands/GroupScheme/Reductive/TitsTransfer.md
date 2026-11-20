# The transfer law for the Tits obstruction

This module proves an integral-weight transfer (corestriction) law for the
Tits obstruction `α`:

`α_k(∑_σ ε σ ⋆ λ) = Cor_{E/k}(α_E(λ_E))`,

for every finite separable extension `E/k` inside `K` and every weight `λ`
fixed by the star action of `Gal(K/E)`, the subgroup of `Gal(K/k)` fixing `E`
pointwise. The sum has one term for each `k`-embedding `σ : E → N`, and
`ε σ ∈ Gal(K/k)` extends `σ`. `Cor` is Task 7575's corestriction homomorphism
`corHom k E : BrauerGroup E →+ BrauerGroup k`
(`Algebra/BrauerCorestriction/Hom`). No hypothesis on the characteristic or
on the size of `k` is used.

**Source and relation to it.** Tits, *Représentations linéaires
irréductibles d'un groupe réductif sur un corps quelconque*, J. reine angew.
Math. 247 (1971), Proposition 5.1 (printed p. 207 / PDF p. 12), concerns the
homomorphism `β_{G,k} : C*^Γ → Br k` on invariant central characters. Let
`c₁ ∈ C*`, let `Γ₁` be its stabilizer in `Γ`, let `k₁` be the fixed field of
`Γ₁`, and let `Θ` be a system of representatives of `Γ/Γ₁`. Then
`β_{G,k}(∑_{θ ∈ Θ} θ(c₁))` is the image of `β_{G,k₁}(c₁)` under the
corestriction `Br k₁ → Br k`. Tits deduces this from the cohomological
description of `β` (§4.3, p. 207) and his reference [14] (printed p. 219 /
PDF p. 24), S. Lang, *Rapport sur la cohomologie des groupes* (1966),
Proposition 13, p. 57, where the corestriction is denoted `tr`. By
Corollary 3.5 (p. 205; see also the end of §4.3), `α_{G,k}` is the composite
of the projection `Λ^Γ → C*^Γ` with `β_{G,k}`.

The theorem of this module is a derived statement about integral weights
over an arbitrary finite separable `E`. It is not Tits's proposition and is
not deduced from it. `E` may be strictly larger than the fixed field of the
stabilizer of `λ`, or of its central character. Terms then repeat, and the
central character of the sum can differ from Tits's `∑_θ θ(c₁)`. For split
`SL₂` over `ℚ`, `E = N = ℚ(√2)` and `λ` the fundamental weight, both
embeddings contribute `λ`. The sum `2λ` has trivial central character, while
Tits's sum for the nontrivial central character `c₁` of `λ` is `c₁` itself.
The proof is this development's own matrix argument:
`Reductive/TitsTransferMatrix` over `k`, `Reductive/TitsTransferBaseChange`
over `E`, and the published identification `cor_mk_eq_of_closure` of the
tensor descent with the corestriction (Task 7575).

Setting: `d` is Galois pinning data for `G` over `K`, `K/k` Galois, and the
coroots span (`hspan`). `E/k` is finite separable, `K/E` Galois, and `N/k`
finite Galois with `[E : k]` embeddings `E → N` (`hN`). Those embeddings are
indexed by `Fin (m + 1)` through `e`, and each `σ` is extended to
`ε σ ∈ Gal(K/k)` (`hε`). `λ_E = weightTransport E λ` is the transported weight
of the base change `d.baseChange E`, with spanning coroots (`hspanE`).

## Declarations (`GaloisPinningData`)

- `starAction_restrictScalars_smul_eq`: if `λ_E` is star-fixed for
  `d.baseChange E`, then `λ` is fixed by the star action of every
  `h ∈ Gal(K/E)` viewed in `Gal(K/k)`. This combines the published
  `baseChange_starAction_weightTransport` with injectivity of the weight
  transport.
- `isDominantWeight_starAction_smul`, `isDominantWeight_sum_starAction_smul`:
  the star action preserves dominance, since it preserves the base
  (`SplitPinning.isDominantWeight_weightMap_iff`). Finite sums of star
  conjugates of a dominant weight are therefore dominant.
- `embeddingConjSum e ε λ` (definition) is the weight `∑_i ε(e⁻¹ i) ⋆ λ`
  of the character lattice: the sum of the star conjugates of `λ` by the
  chosen automorphisms `ε σ`, one term for each embedding `σ : E → N`, so a
  weight is counted again when two embeddings give the same conjugate. It is
  a derived integral-weight analogue of the sum `∑_{θ ∈ Θ} θ(c₁)` of Tits's
  Proposition 5.1, using all embeddings of the chosen `E` rather than the
  cosets of the exact stabilizer of a central character (see above).
  `embeddingConjSum_eq` unfolds it (`rfl`); the theorems below state the sum
  explicitly.
- `isStarFixedWeight_sum_conj` (**star invariance**): if `λ_E` is star-fixed,
  then `∑_i ε(e⁻¹ i) ⋆ λ` is fixed by the star action of `Gal(K/k)`. For
  `τ ∈ Gal(K/k)` with restriction `g` to `N`,
  `τ · ε σ = ε(g ∘ σ) · h` with `h ∈ Gal(K/E)`
  (`stabCorrection_restrictScalars`), and `h` fixes `λ`. So `τ` permutes the
  terms along `σ ↦ g ∘ σ` (`galPerm`).
- `titsObstructionValue_transfer_of_isDominantWeight`: the transfer law for
  dominant `λ`. Take `ρ` of highest weight `λ` (published classification) and
  intertwiners `Q h : ρ → ρ^h` for `h ∈ Gal(K/E)`
  (`exists_intertwiner_galoisTwist_of_smul`). Then:
  - `titsObstructionValue_baseChange_eq_classOf` gives
    `α_E(λ_E) = [A]` for `A = toCSA Q (twistedFixed Q)`;
  - `cor_mk_eq_of_closure` gives `Cor_{E/k}[A] = [corCSAOf k E N A]`;
  - `titsObstructionValue_eq_classOf_corCSAOf` gives
    `α_k(∑_i ε(e⁻¹ i) ⋆ λ) = [corCSAOf k E N A]`.
- `titsObstructionValue_transfer` (**transfer law**): for every `λ` with
  `λ_E` star-fixed for `d.baseChange E`,
  `titsObstructionValue d (∑_i ε(e⁻¹ i) ⋆ λ) = corHom k E (titsObstructionValue (d.baseChange E) λ_E)`.
  Write `λ_E = a - b` with `a`, `b` dominant and star-fixed for
  `d.baseChange E` (`exists_dominant_sub`), and pull `a`, `b` back along the
  weight transport. Dominance is preserved because the root-datum equivalence
  preserves the base. Both sides are additive: on the left by
  `titsObstructionValue_eq_sub` and `titsObstructionValue_of_isDominantWeight`
  for the dominant sums of conjugates, on the right by additivity of
  `corHom` and the same lemmas for `d.baseChange E`. So the dominant case
  applies to `a` and `b`.
- `titsObstructionValue_embeddingConjSum`: the same identity with the
  left-hand weight written as `d.embeddingConjSum e ε λ`.

## Scope

The sum is indexed by the embeddings `E → N` through `e` and the chosen
extensions `ε`. Its expression as a sum over one representative of each
coset of `Gal(K/k)/Gal(K/E)`, and the specialization to the fields of the
Tits index, are not stated here.
