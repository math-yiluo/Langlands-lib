# Noetherianity of inductions from an actual represented Levi along embeddings

Module `Langlands.Representation.Exponents.LeviInductionNoetherian`.

## Purpose and scope

Renard, *Représentations des groupes réductifs p-adiques* (9 July 2026 version), VI.7.5,
Theorem (printed p.187 / PDF p.193), proves that `i_P^G` preserves finite type. In the
general case, the proof embeds a finitely generated `ρ` into a finite direct sum
`⊕_{P'} i_{P'}^M(ρ_{M'})` (VI.7.2 Lemma). It then applies the exact functor `i_P^G`,
uses transitivity of induction, and uses the supercuspidal case. The conclusion is that
`i_P^G(ρ)` is a subobject of a finite sum of Noetherian representations, hence Noetherian.

This module proves the descent part of that step for the represented-parabolic interface.
Let `p : P ⟶ G`, `l : M ⟶ P`, `r : U ⟶ P` be an actual rational parabolic triple with the
hypotheses of `leviInductionFunctor`. Suppose a smooth representation `A` of `M(F)` admits
a finite jointly injective family of intertwiners `A → B i` (for instance the components
of an embedding into `⊕ B i`), and every `i_P^G(B i)` is Noetherian over `ℂ[G(F)]`. Then
`i_P^G(A)` is Noetherian, and in particular finitely generated over `ℂ[G(F)]`.

"Noetherian" means that the group-algebra module `ρ.asModule` is a Noetherian module
(`IsNoetherian`).

The module proves neither VI.7.5 target. It does not construct the embedding, does not
identify `i_P^G ∘ i_{P'}^M` with an induction from `G`, and does not prove the
supercuspidal case. All three are explicit premises or later steps.

## Declarations

### Generic (namespace `Langlands.NoetherianRepresentation`)

`k` is a commutative ring and `G` a monoid. The index type and the carriers have
independent universes.

- `piMap f` (definition): for a family of intertwiners `f i : ρ → σ i`, the `k[G]`-linear
  map `ρ.asModule →ₗ[k[G]] Π i, (σ i).asModule` with components the `k[G]`-linear maps
  of the `f i`. These come from `Representation.IntertwiningMap.equivLinearMapAsModule`,
  which keeps the underlying function. `piMap_apply`: the `i`th component of
  `piMap f v` is `f i v`, by `rfl`.
- `piMap_injective_iff`: `piMap f` is injective if and only if the family is jointly
  injective, i.e. `f i x = f i y` for every `i` forces `x = y`.
- `of_jointlyInjective`: for a finite index type, if the family is jointly injective and
  every `σ i` is Noetherian, then `ρ` is Noetherian. Proof: `piMap f` is injective, and
  its target is Noetherian by Mathlib's `isNoetherian_pi`. Conclude with
  `isNoetherian_of_injective`.

### Direct sums (namespace `Langlands.SmoothRep`)

- `directSum_components_jointlyInjective`: let `f` be an injective intertwiner from `A`
  into the published actual direct sum `SmoothRep.directSum B`. Then its compositions
  with the summand projections `directSumπ B i` are jointly injective. Proof:
  `DirectSum.ext_component`.

### Represented parabolics (namespace `Langlands.Aubert.General.RepresentedParabolic`)

The variables are those of the published `leviInductionMap`
(`Exponents/LeviInductionEmbeddings.lean`): a field `k` with a Hausdorff topology,
group schemes with affine structure morphisms for `G` and `M`, the canonical point
topologies, `G(F)` locally compact and nonarchimedean, and an actual rational parabolic
triple `(p, l, r)` with `hp`, `hl`, `hr`, `hmul`.

- `leviInductionMap_jointlyInjective`: let `f i : A → B i` be jointly injective, where
  the `B i` may have a different carrier universe from `A`. Then the induced intertwiners
  `leviInductionMap … (f i)` on `i_P^G(A)` are jointly injective. Proof: induced functions
  are compared pointwise. If all images of `x` and `y` agree, then for every `g ∈ G(F)`
  the values `x(g)` and `y(g)` have equal images under every `f i`, so `x(g) = y(g)`.
  This extends the published `leviInductionMap_injective` to families.
- `leviInduction_isNoetherian_of_jointlyInjective`: let `J` be finite and `f i : A → B i`
  jointly injective. If every `(leviInductionFunctor …).obj (B i)` is Noetherian over
  `ℂ[G(F)]`, then `(leviInductionFunctor …).obj A` is Noetherian. Proof: combine the
  previous lemma with `of_jointlyInjective`.
- `leviInduction_isNoetherian_of_injective_directSum`: the same conclusion for an
  injective intertwiner `A → SmoothRep.directSum B`, with `J` finite and decidable
  equality on `J`. Proof: use the summand components.
- `leviInduction_finite_of_injective_directSum`: under the same hypotheses,
  `(leviInductionFunctor …).obj A` is finitely generated over `ℂ[G(F)]`. Proof: Mathlib's
  instance `IsNoetherian.finite`. The conclusion has the form of the conclusion of
  `LeviInductionFiniteTypeStatement`.

## Provenance

The statements are derived. They isolate the descent part of the general step of Renard's
proof, together with the elementary fact that a Noetherian module is finitely generated.
The pointwise argument follows the published `Langlands.Induction.smoothInducedMap_injective`.
