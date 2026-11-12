# Realization of Galois lattices by tori: statement

Worker 3483.

`Langlands.GroupScheme.TorusGaloisLatticeRealizationStatement.{u}` is a
proposition definition. This module does not prove it.

## The statement

Let `k` and `L` be fields in the universe `u`, with `L` a finite Galois
extension of `k` (`[Algebra k L] [FiniteDimensional k L] [IsGalois k L]`). Let
`M : Type u` be an abelian group that is a free `ℤ`-module of finite rank
(`[Module.Free ℤ M] [Module.Finite ℤ M]`), and let
`ρ : Representation ℤ (L ≃ₐ[k] L) M` be a `ℤ`-linear action of the Galois
group `Gal(L/k) = L ≃ₐ[k] L` on `M`. The statement asserts that there exist

- a commutative group scheme `T : CommGroupScheme (Spec (CommRingCat.of k))`,
  and
- an additive isomorphism `e : M ≃+ X^*(T_L)`, where
  `T_L = (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T` and
  `X^*(T_L) = characterLattice T_L` is the group of homomorphisms
  `T_L ⟶ 𝔾_m` over `Spec L` (`Torus/Lattice`),

such that

1. `IsSplitTorus T_L.toGrp`: the base change `T_L` is isomorphic, as a group
   scheme over `Spec L`, to `splitTorus (Spec L) I` for a finite type `I`
   (`Torus/Split`; `I` may be empty); and
2. `e (ρ σ m) = characterLattice.galoisRepresentation k L T σ (e m)` for every
   `σ ∈ Gal(L/k)` and `m ∈ M`: `e` intertwines `ρ` with the Library's Galois
   action on characters (`Torus/LatticeGalois`), which on points is
   `(σ χ)(t) = σ (χ (σ⁻¹ t))`.

In words: every finitely generated free `ℤ[Gal(L/k)]`-lattice is, up to
equivariant isomorphism, the character lattice of a torus over `k` split by
`L`.

## Source

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
over a Field* (2017), source ID `milne-2017-algebraic-groups`, §12.g
(printed pp.239–240, PDF pp.255–256).

§12.g defines the Galois module of an algebraic group (printed p.239,
PDF p.255):

> Let Γ denote the Galois group of k_s/k endowed with the Krull topology. An
> action of Γ on a commutative group M is continuous for the discrete topology
> on M if every element of M is fixed by an open subgroup of Γ, i.e.,
> M = ⋃_K M^{Gal(k_s/K)} where K runs through the finite extensions of k
> contained in k_s.
> For an algebraic group G, we let X^*(G) = X(G_{k_s}). In other words, X^*(G)
> consists of the characters of G defined over k_s.

Printed p.240 (PDF p.256):

> The tori are the groups G of multiplicative type such that X^*(G) is
> torsion-free.

> THEOREM 12.23. The functor X^* is a contravariant equivalence from the
> category of algebraic groups of multiplicative type over k to the category
> of finitely generated Z-modules equipped with a continuous action of Γ (with
> quasi-inverse M ⇝ D(M)). Under the equivalence, short exact sequences
> correspond to short exact sequences.

Example 12.27 (printed p.241, PDF p.257) shows both actions of
`Gal(ℂ/ℝ)` on `ℤ`: the trivial one gives `𝔾_m`, and `m ↦ -m` gives the torus
with real points `{z ∈ ℂ^× | z z̄ = 1}`.

## Correspondence with the source

The Lean statement is the essential surjectivity part of Theorem 12.23,
restricted to tori and to actions that factor through a finite Galois
extension. It is a **derived** formulation, for the following reasons.

- **Tori.** Milne's category contains all groups of multiplicative type, with
  any finitely generated `M`. The statement takes `M` free of finite rank,
  which for a finitely generated abelian group is the same as torsion-free.
  By the sentence quoted above these are exactly the Galois modules of tori.
  The torsion case and the realizing group `D(M)` of multiplicative type are
  not formalized.
- **Finite Galois level.** A continuous action of `Γ = Gal(k_s/k)` on a
  finitely generated `M` fixes each of finitely many generators on an open
  subgroup, so it factors through `Gal(L/k)` for some finite Galois `L/k`
  inside `k_s`. Conversely, `ρ` inflates to a continuous action of `Γ`. The
  statement works at this finite level, with the characters of `T_L` in place
  of the characters of `T_{k_s}`: once `T_L` is split, every character of
  `T_{k_s}` is defined over `L`.
- **Realization by a torus split by `L`.** Applying Theorem 12.23 to the
  inflated action gives a torus `T` over `k` with `X^*(T) ≅ M` equivariantly.
  The subgroup `Gal(k_s/L)` acts trivially on `M`, so `T_L` corresponds to the
  trivial `Gal(k_s/L)`-module and is split. Hence `T_L` is a split torus and
  `X^*(T_L) ≅ M` as `Gal(L/k)`-modules, which is the Lean conclusion. So the
  statement is true and is a consequence of Theorem 12.23.
- **The action.** Milne does not write a formula for the action of `Γ` on
  `X^*(G)` in §12.g. The Library's `characterLattice.galoisRepresentation` is
  transport along `Spec σ`, which on points is the standard left action
  `(σ χ)(t) = σ (χ (σ⁻¹ t))` (see `Torus/LatticeGalois.md`). The derivation
  above reads Theorem 12.23 with this action.
- **Only existence.** The statement asserts the existence of a realizing
  torus. It does not name Milne's quasi-inverse
  `D(M) = Spec (k_s[M])^Γ`, it does not assert functoriality, and it does not
  include the clause about short exact sequences. The isomorphism `e` is part
  of the data that is asserted to exist, so the realization is equivariant,
  not merely an abstract isomorphism of groups.
- **Universes.** `M` lies in the universe `u` of `k`; every finitely
  generated abelian group has a copy there, so nothing is lost.

## Relation to the Library

- The Library proves the other half of the anti-equivalence for tori split by
  `L` (`Torus/FiniteGaloisCharacterDescent`, same hypotheses on `k` and `L`):
  - `IsSplitTorus.existsUnique_hom_of_equivariant_characterMap`: if
    `T'_L` is split, every `Gal(L/k)`-equivariant additive map
    `X^*(T'_L) →+ X^*(T_L)` is the character pullback of exactly one
    homomorphism `T ⟶ T'` over `k` (full faithfulness);
  - `IsSplitTorus.exists_iso_of_equivariant_characterEquiv`: if `T_L` and
    `T'_L` are split, every equivariant additive isomorphism
    `X^*(T'_L) ≃+ X^*(T_L)` comes from an isomorphism `T ≅ T'`.

  The second theorem shows that the torus asserted to exist here is unique up
  to isomorphism. Once this statement is proved, the three results together
  give the contravariant equivalence between commutative group schemes over
  `k` whose base change to `L` is a split torus and free finite-rank
  `ℤ`-lattices with a `Gal(L/k)`-action.
- Special cases are already realized. Taking `Ω = L` in
  `WeilGm.separableEmbeddingCharacterEquiv_galoisRepresentation`
  (`Torus/WeilRestrictionSeparable`), the Weil restriction `Res_{K/k} 𝔾_m` of a
  finite separable extension `K/k`, such that the minimal polynomial over `k`
  of every element of `K` splits in `L`, has
  character lattice `(K →ₐ[k] L) → ℤ` with `Gal(L/k)` permuting the
  embeddings. These are permutation lattices; a general lattice is not of this
  form.
- No Library declaration of the statement was found: no theorem has type
  `TorusGaloisLatticeRealizationStatement`. A search of `Langlands/` for
  `characterLattice.galoisRepresentation`, for `ℤ`-representations as
  hypotheses, and for statements asserting the existence of a commutative
  group scheme found no existence result for a prescribed action; the latter
  all produce subgroups of a given group. The published family-2 ledger
  (`notes/group-schemes/ledger-family-2-tori.md`, row D4) lists the
  Galois-module classification as a gap; this statement supplies its torus
  existence part.
- Library results a proof can build on:
  `Descent.SemilinearComponents.datumOfSemilinear`
  (`Descent/SemilinearDatum`) builds descent data along `Spec L ⟶ Spec k`
  from a family of semilinear isomorphisms `σ^* G ≅ G` satisfying the tower
  law; `affineGroupSchemeFiniteGaloisDescent` (`Descent/AffineEffectivityProof`)
  proves that such data on an affine group over a finite Galois extension are
  effective. Applied to a split torus over `L` with character lattice `M`,
  twisted by `ρ`, these give a candidate `T`. The descent-data constructions
  from a split pinning in `Reductive/PinnedGaloisDatum` use the same method.
