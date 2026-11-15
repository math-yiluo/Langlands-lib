# Ternary special linear homomorphisms over partnered orbits of simple roots

Module `Langlands.GroupScheme.Rational.PartnerOrbitSpecialUnitary`, namespace
`Langlands.GroupScheme.SplitPinning`.

Worker 163, for Task 6836 (8c04a3ed-3fa6-4680-a59f-856738cb578b), SU3 half.

## Purpose

This module builds the homomorphism `SU₃(L/E) → G(k)` attached to a set `O` of simple roots
that falls into `A₂` pairs. It is the `SU₃` analogue of the `SL₂` homomorphism
`fieldSL2` of `OrthogonalOrbitSpecialLinear`. The construction follows the standard one for
quasi-split groups:

1. over a splitting field `K`, each `A₂` pair `{r, π r}` of simple roots gives a
   homomorphism `SL₃(K) → G(K)`;
2. distinct pairs are mutually orthogonal, so these homomorphisms have commuting images;
3. their product, evaluated at the embedding coordinates of a matrix over `L`, is fixed by
   Galois and descends to `G(k)`.

See Borel–Tits, *Groupes réductifs* §4, and Kaletha–Prasad, *Bruhat–Tits theory*,
Prop. 7.1.1 and its proof. The Lean development is internal. It assumes the statement
`AdjacentSimpleRootSpecialLinearStatement` (hypothesis `hAdj`) and does not prove it.
Every other step is proved here or taken from the Library.

The constructions take only a set `O` with a partner structure (`PartnerData`) and abstract
embeddings `τ`. They do not refer to a relative root. The module
`SimpleRootFiberPartners` provides these inputs for the simple-root fiber of a multipliable
relative root.

## Split part (section `Split`)

Variables: a field `k`, an affine group scheme `G` over `k`, a split pinning `p` of `G` with
normalized simple-root parametrizations `x`, and `hAdj : AdjacentSimpleRootSpecialLinearStatement`.

- `pairSL3 hAdj x a b : SL₃(k) →* G(k)` (def). If `⟨a, b^∨⟩ = ⟨b, a^∨⟩ = -1`, it is the
  homomorphism chosen by `hAdj`; otherwise it is the trivial homomorphism.
- `pairSL3_spec`, `pairSL3_left`, `pairSL3_right`: for such a pair, `pairSL3` restricts to
  `rootSL2 x a` on the upper-left block `TernaryPresentation.left` and to `rootSL2 x b` on
  the lower-right block `TernaryPresentation.right`.
- `eq_pairSL3`: every homomorphism with these two restrictions equals `pairSL3`
  (`TernaryPresentation.hom_ext`).
- `pairSL3_swap`: `pairSL3 hAdj x b a = (pairSL3 hAdj x a b).comp TernaryPresentation.outer`.
  The outer involution swaps the two blocks (`outer_comp_left`, `outer_comp_right`), so this
  follows from uniqueness.
- `pairSL3_mem`: every value lies in `(rankData x a).rootSubgroup ⊔ (rankData x b).rootSubgroup`.
  The blocks generate `SL₃(k)` (`range_left_sup_range_right`), and `rootSL2_mem` places the
  block values in the root subgroups.
- `rootSubgroup_le_centralizer`: for distinct orthogonal simple roots `a ≠ c`, the root
  subgroup of `a` centralizes that of `c`. This uses `rootsCommute_of_orthogonal` from
  `OrthogonalOrbitCorootWords` on the set `{a, c}`.
- `pairSL3_commute`: if `{a, b}` and `{c, d}` are `A₂` pairs, every root of the second pair
  differs from every root of the first, and each such pair of roots is orthogonal, then all
  values of `pairSL3 hAdj x a b` commute with all values of `pairSL3 hAdj x c d`.

### Partner data (namespace `PartnerData`)

- `PartnerData O` (structure) for `O : Set p.base.support`. Its fields are a map `partner` on
  simple roots with these properties on `O`: it preserves `O` (`mem`), is involutive
  (`partner_partner`) and has no fixed points (`ne`). Each `a ∈ O` pairs to `-1` with
  `partner a` in both directions (`pairing`). Every `b ∈ O` other than `a` and `partner a`
  is orthogonal to `a` (`orthogonal`).
- `orientation D`: the members `a ∈ O` with `WellOrderingRel a (partner a)`. This picks one
  member of each pair. `mem_of_mem_orientation`; `mem_orientation_iff` (for `a ∈ O`,
  `a` is in the orientation iff `partner a` is not); `partner_mem_orientation`.
- `normalize D a`: `a` if `a` is in the orientation, else `partner a`.
  `normalize_mem` (in the orientation for `a ∈ O`), `normalize_of_mem`, `normalize_eq`
  (it is `a` or `partner a`).
- `commute`: for distinct `r, r'` in the orientation, all values of
  `pairSL3 hAdj x r (partner r)` and `pairSL3 hAdj x r' (partner r')` commute.
- The orientation is finite (`Fintype` instance from `Finite`, since the simple roots are
  finite).
- `pairOrbitSL3 D hAdj x : (p.base.support → SL₃(k)) →* G(k)` (def). It is the commuting
  product `MonoidHom.noncommPiCoprod` over `r` in the orientation of
  `pairSL3 hAdj x r (partner r)` evaluated at the coordinate `h r`.
  `pairOrbitSL3_apply` writes it as `Finset.univ.noncommProd`. `pairOrbitSL3_congr` says it
  depends only on the values of `h` on `O`.
- `IsPairFamily D h`: `h (partner a) = outer (h a)` for all `a ∈ O`.
- `pairSL3_partner_eq`, `pairSL3_normalize_eq`: on a pair family, the pair `a, partner a`
  and the pair `partner a, a` give the same value, by `pairSL3_swap` and `outer_outer`. So
  the normalized representative gives the same value too.

`noncommProd_univ_equiv`: a commuting product over `Finset.univ` of a finite type is
unchanged when the index is reindexed by a permutation (`Multiset.map_univ_val_equiv`).

## Galois part (section `Galois`)

Variables as in the Galois section of `OrthogonalOrbitSpecialLinear`:

- a field extension `K/k` and a torus morphism `i : T ⟶ G` over `k`;
- a split pinning `p` of `G_K` whose torus is identified with `T_K` by `eT`, with
  `hT : p.inclusion = eT.hom ≫ i_K`;
- normalized parametrizations `x` and an action `ρ` of `Aut(K/k)` on the simple roots,
  Galois compatible with `x` (`hx : RootMapsGaloisCompatible k K p x ρ`) and transporting
  roots by the Galois representation on characters (`hroot`).

Two more hypotheses are added: `hAdj`, and `hρpair` (the action `ρ` preserves pairings).
The local instance `partnerOrbitSpecialUnitaryIsAffineHom` records that `G_K` is affine
over `K`.

- `pairSL3_rationalConjugate`: for an `A₂` pair `a, b`, conjugating the coefficients of
  `pairSL3 hAdj x a b g` by `σ` gives `pairSL3 hAdj x (ρ σ a) (ρ σ b) (σ g)`. Both sides are
  homomorphisms of `g`, and they agree on the two blocks by `TernaryPresentation.map_left`,
  `map_right` and `rootSL2_rationalConjugate`. Then `hom_ext` applies.

Further variables: `D : PartnerData O`, with `O` stable under `ρ` (`hOs`) and the partner
map commuting with `ρ` on `O` (`hπρ`).

- `pairFamilies k K p D ρ` (def): the subgroup of families `h : p.base.support → SL₃(K)`
  that are pair families and Galois equivariant, meaning `h (ρ σ a) = σ (h a)` for all
  `σ` and `a`.
- `normalize_action_injective`: `r ↦ normalize (ρ σ r)` is injective on the orientation, so
  it is a permutation of the orientation.
- `pairOrbitSL3_rationalConjugate`: for `h ∈ pairFamilies`, `pairOrbitSL3 D hAdj x h` is
  fixed by every `rationalConjugate σ`. Each factor moves to the factor at
  `normalize (ρ σ r)` (by `pairSL3_rationalConjugate`, equivariance, `hπρ` and
  `pairSL3_normalize_eq`). The product is then reindexed by `noncommProd_univ_equiv`.

### Descent (section `Descent`, `K/k` finite Galois)

- `exists_pairOrbitSL3_eq_rationalExtend`: the fixed product is the base change of a
  rational point of `G`, by `exists_rationalExtend_eq_of_fixed` from `OrthogonalOrbitDescent`.
- `pairOrbitRational … : pairFamilies k K p D ρ →* G(k)` (def): the chosen descent. It is a
  homomorphism because `rationalExtend_injective_of_isAffineHom` makes base change
  injective.
- `rationalExtend_pairOrbitRational`: its base change is `pairOrbitSL3 D hAdj x h`.

### Field coordinates (section `Field`)

Variables: a field `L` over `k`, embeddings `τ : p.base.support → (L →ₐ[k] K)` and a ring
involution `c` of `L` (`SU3Root.RingInvolution L`). The hypotheses are:

- `hτ`: for `a ∈ O`, `τ (ρ σ a) = σ ∘ τ a`;
- `hτc`: for `a ∈ O`, `τ (partner a) y = τ a (c.bar y)`.

- `specialLinearMap_comp_three`: `SL₃` coefficient maps compose.
- `fieldFamilyThree k K p τ : SL₃(L) →* (p.base.support → SL₃(K))` (def): the family
  `a ↦ τ a (g)` on `O`, trivial off `O`. `fieldFamilyThree_apply`, `fieldFamilyThree_of_mem`.
- `fieldFamilyThree_mem`: for `g` in `SU3Root.twistFixedSubgroup c`, the family lies in
  `pairFamilies`. Galois equivariance comes from `hτ` and `hOs`. The pair-family property
  comes from `hτc` together with `TernaryPresentation.map_outer` and
  `outer_eq_map_of_mem_twistFixedSubgroup`: on the twist-fixed subgroup, the outer
  involution is entrywise conjugation by `c`.
- `fieldSU3 … : SU3Root.twistFixedSubgroup c →* G(k)` (def): `pairOrbitRational` composed
  with `fieldFamilyThree` restricted to the twist-fixed subgroup.
- `rationalExtend_fieldSU3`: the base change of `fieldSU3 g` is
  `pairOrbitSL3 D hAdj x (fun a => τ a (g))`.
- `unitaryRho … : SU3Root.specialUnitarySubgroup c →* G(k)` (def): `fieldSU3` composed with
  the inverse of `SU3Root.fixedSpecialUnitaryEquiv c`. This is the special unitary group in
  the form used by `AlgebraicSU3RootCoordinates.rho`.
- `rationalExtend_unitaryRho`: its base change is
  `pairOrbitSL3 D hAdj x (fun a => τ a ((fixedSpecialUnitaryEquiv c).symm g))`.

## Scope

The module defines the homomorphism and computes its base change. The values on upper and
lower unipotent, diagonal and Weyl elements, and the identification of root subgroups, come in
later modules. The module does not prove `AdjacentSimpleRootSpecialLinearStatement`.

## Imports

`Langlands.GroupScheme.Rational.OrthogonalOrbitSpecialLinear` (Library) and
`Langlands.GroupScheme.Rational.AdjacentSimpleRootSpecialLinearStatement` (Worker 195's
accepted candidate `d1e8d725`, which also brings in
`Langlands.GroupScheme.SpecialLinearTernaryPresentation`).
