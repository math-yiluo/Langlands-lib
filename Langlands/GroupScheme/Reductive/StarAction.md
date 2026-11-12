# The star action on a based root datum

Author: Worker 15, for the algebraic and reductive group-scheme program
`2b5e4a00-9d44-49a4-9c89-979fb5b6233e` (Task 3483).

This module constructs the star action of `E ≃ₐ[k] E` on a based root datum of a
reductive group `G` over a field `k`. It is built from a torus of `G` defined over
`k`, by correcting the ordinary Galois action on the torus lattices with the Weyl
group. Let `k` and `E` be fields in one universe `u`, with an algebra `k → E`. Write
`G_E`, `T_E` and `i_E` for actual base changes along `algebraBaseMap k E`.

## Data

`GaloisPinningData k E G` is a structure for an actual group scheme `G` over
`Spec k` with affine structure morphism. Its fields are:

- a commutative group scheme `torus = T` over `Spec k` and a homomorphism
  `inclusion = i : T ⟶ G` over `k`;
- `IsConnectedReductive G_E`;
- `T_E` is a split torus, and `i_E` is a maximal torus of `G_E`;
- a finite root-index type, a root datum `rootDatum = P` on the actual character and
  cocharacter lattices of `T_E`, with `IsRootDatumOf i_E P`, `P` reduced;
- a base `base` of `P` and a `RootPinning` of `i_E` relative to `P` and `base`.

These are the fields of the Library's `SplitPinning` of `G_E`, except that the torus
and its inclusion are the base changes of a torus and a homomorphism defined over
`k`. `GaloisPinningData.toSplitPinning` is that split pinning, with the same root
datum.

The data are supplied, not constructed. The Library proves that every smooth affine
group over `k` has a maximal torus over `k` (`maximalTorusExistence`), and that every
torus splits over a finite Galois extension (`torusFiniteGaloisSplitting`). Existence of
the full data, including the root datum and the pinning, is a separate statement.

## Constructions

Assume moreover `[LocallyOfFiniteType G.X.hom]`.

- `GaloisPinningData.galoisAction d : (E ≃ₐ[k] E) →* P.Aut` is the published
  `IsRootDatumOf.galoisRootDatumActionOfClosedSplitTorus` (module
  `Reductive/RootDatumGaloisCoroots`). An automorphism `σ` acts on characters of
  `T_E` by `characterLattice.galoisRepresentation k E T σ`. The contravariant coweight
  map is the cocharacter action of `σ⁻¹`, and roots are permuted accordingly. This is
  the natural Galois action on the lattices of the chosen torus `T`, defined over `k`.
- `GaloisPinningData.starAction d : (E ≃ₐ[k] E) →* p.basedRootDatumAut`, with
  `p = d.toSplitPinning`, is the composite of `galoisAction` with the published
  Weyl-correction homomorphism `SplitPinning.basedRootDatumProjection`
  (`Reductive/BasedRootDatumProjection`). Its target is the group of automorphisms
  of `P` that preserve the support of the chosen base.

`basedRootDatumProjection δ` is the unique automorphism preserving the base in the
left Weyl coset of `δ`. Hence `starAction σ = w_σ · galoisAction σ`, where `w_σ` is
the unique element of the Weyl group of `P` for which the product preserves the base.
The homomorphism property comes from `basedRootDatumProjection` being a homomorphism
whose kernel is the Weyl group.

## Source

Milne, *Algebraic Groups* (2022 corrected reprint), source `milne-2022-algebraic-groups`,
SHA-256 `f2ddd8fa4d263085f173934664b246007a2c0bd539739b7c82de39bfb5d21f40`:

- §25.c, printed p.555 (PDF p.566), defines the `*`-action. Take a maximal torus `T`
  of `G` over `k`, so that `(G, T)` is split over `k_s`, and let `Γ = Gal(k_s/k)`.
  Then `Γ` acts naturally on `X^*(T)` and `X_*(T)`, preserving the roots and coroots.
  For `σ ∈ Γ`, `σ(Δ)` is again a base, so "`w_σ(σ(Δ)) = Δ` for a unique `w_σ ∈ W`".
  For `α ∈ Δ`, Milne puts `σ * α = w_σ(σα)`. "It is called the `*`-action." Milne takes
  `T` to contain a maximal split torus. That condition matters only for the Tits
  index, not for the definition of the action.
- 23.75, printed p.513 (PDF p.524): the automorphisms of a root datum respecting a
  base project isomorphically onto `Out(R)` and meet the Weyl group trivially, so
  `Aut(R) = W ⋊ Aut(R₊)`.

`starAction σ` is Milne's `w_σ ∘ σ`, as an automorphism of the whole based root
datum. `galoisAction σ` is Milne's natural action of `σ` on `X^*(T)`, `X_*(T)` and the
roots. `basedRootDatumProjection` is the projection `Aut(R) → Aut(R₊)` of 23.75.
Proposition 25.28(a) on the same page states that the `*`-action is the natural action
when `G` is quasi-split. The lemma `starAction_eq_galoisAction` below is the
root-datum part of that statement. It assumes that `σ` preserves the base, which is
the case when the base comes from a Borel subgroup defined over `k`.

## Lemmas

- `starAction_mul_galoisAction_inv_mem`: `(starAction σ) * (galoisAction σ)⁻¹` lies in
  the Weyl group of `P`.
- `exists_weyl_mul_galoisAction_eq_starAction`: some Weyl element `w` satisfies
  `w * galoisAction σ = starAction σ`.
- `starAction_eq_galoisAction`: if `galoisAction σ` preserves the base, then
  `starAction σ = galoisAction σ`.
- `starAction_eq_one_iff`: `starAction σ = 1` exactly when `galoisAction σ` lies in the
  Weyl group.

Each lemma is the corresponding published property of
`basedRootDatumProjection`, applied to `galoisAction σ`.

## Scope

`E` is an arbitrary field extension of `k`, and `E ≃ₐ[k] E` is the full automorphism
group. No finiteness, separability or Galois hypothesis is used. For the absolute
based root datum take `E` to be a separable closure of `k`. Then `E ≃ₐ[k] E` is the
absolute Galois group, and the construction gives the star action on the based root
datum `(X^*(T_E), Δ, X_*(T_E), Δ^∨)`. The following are separate statement
obligations: independence of the choices of `T` and of the pinning (up to the
isomorphisms induced by `G(E)`-conjugation), continuity for the Krull topology, and
existence of the data. This module asserts none of them.

Milne's `*`-action is a continuous action of `Gal(k_s/k)` on `Δ`. Here the acting group
is `E ≃ₐ[k] E` for the supplied `E`, and the action is on the whole based root datum,
not only on `Δ`. The two agree on `Δ` when `E = k_s`. The module composes two
published constructions, and introduces no new assertion beyond the four lemmas
listed above.
