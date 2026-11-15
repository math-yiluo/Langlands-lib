# Products of positive root points over arbitrary rings

This module extends the local result of
`Langlands.GroupScheme.Reductive.LocalSplitPositiveCell` from local test rings to
arbitrary commutative test rings. It also adds uniqueness of the coordinates. Take a
split reductive group over an arbitrary commutative ring. Then a finite product of
positive root points over any test ring `B` is a product of the positive big-cell
factors, `∏ₖ u_{pos k}(z k)`, for exactly one coordinate vector `z` with entries in
`B`. Taking `B` to be a polynomial ring later gives polynomial formulas for products
in the positive cell factor.

## Statement

`LocalSplitPositiveProductRingStatement.{u}` has the same data as
`LocalSplitPositiveProductStatement`, except that the test ring is arbitrary and the
conclusion is unique existence:

- a commutative ring `R`, a finite type `I` and a type `J`, all in universe `u`;
- a reductive group scheme `G` over `Spec R`, with the instance binder `IsAffineHom`
  for its structure morphism;
- a coordinate split torus `i : T_I → G` that is maximal on every residue-field
  fibre, and a coordinate root datum `P : RootDatum J (I → ℤ) (I → ℤ)` that is a
  fibrewise root datum for `i`, with a base `b`;
- a family `u : J → (𝔾ₐ ⟶ G)` with `u α` a root parametrization of `i` for
  `P.root α` for every root `α`;
- enumerations `neg : Fin m ≃ {α // ¬ b.IsPos α}` and `pos : Fin n ≃ {α // b.IsPos α}`.
  Only `pos` occurs in the conclusion;
- a commutative ring `B : Type u` (not necessarily local), a morphism
  `s : Spec B ⟶ Spec R`, a list `e : Fin r → J` of positive roots and global
  functions `c : Fin r → Γ(Spec B, ⊤)`.

The conclusion is that there is exactly one `z : Fin n → Γ(Spec B, ⊤)` with

`u_{e 0}(c 0) · … · u_{e (r-1)}(c (r-1)) = u_{pos 0}(z 0) · … · u_{pos (n-1)}(z (n-1))`

as points of `G` over `s`. The module proves this proposition at full universe as
`localSplitPositiveProductRing`.

The namespace `LocalSplitCell` also contains:

- `eq_zero_of_specLocalization`: a global function on `Spec B` is zero if its
  restrictions to `Spec B_𝔪` vanish for all maximal ideals `𝔪`;
- `specMap_algebraMap_closedPoint`: the closed point of `Spec B_𝔭` maps to `𝔭`;
- `mkCellPoint_zero_one_comp_cellMap`: `∏ₖ u_{pos k}(z k)` is the image under the cell
  map of the cell point with zero negative coordinates, trivial torus coordinate and
  positive coordinates `z`;
- `orderedProduct_pos_injective`: if the cell map is an open immersion, the
  coordinates of `∏ₖ u_{pos k}(z k)` are unique, over any test object;
- `exists_orderedProduct_eq_pos_of_ring` and `existsUnique_orderedProduct_eq_pos_of_ring`:
  the existence and unique-existence statements for any family `u`, any enumerations
  whose cell map is an open immersion, and any torus equivariance
  `TorusEquivariant i ch u`. One needs a cocharacter `ν` with
  `⟨ch (neg k), ν⟩ < 0` for all `k` and `⟨ch (e k), ν⟩ > 0` for all `k`, as in the
  imported `exists_orderedProduct_eq_pos`;
- `existsUnique_orderedProduct_eq_pos_of_isPos`: the root-family form used by the
  proposition.

## Proof

**Uniqueness.** By `comp_cellMap`, the cell point with coordinates `(0, 1, z)` maps
to `1 · 1 · ∏ₖ u_{pos k}(z k)` (`mkCellPoint_zero_one_comp_cellMap`). An open
immersion is a monomorphism. So equal products give equal cell points, and the
positive coordinates of these cell points are `z` and `z'`.

**Existence.** Let `g = ∏ₖ u_{e k}(c k)` over `Spec B`. For every prime `𝔭` of `B`,
pull `g` back along `Spec B_𝔭 → Spec B`. It becomes the product of the same root
points with the restricted coordinates (`comp_orderedProduct`). The imported local
result `exists_orderedProduct_eq_pos` writes it as `∏ₖ u_{pos k}(z_𝔭 k)`, that is, as
the cell point `(0, 1, z_𝔭)` composed with the cell map. The closed point of
`Spec B_𝔭` maps to `𝔭`, by Mathlib's `Localization.AtPrime.under_maximalIdeal`. So
`g` maps every point of `Spec B` into the image of the open immersion. Mathlib's
`IsOpenImmersion.lift` then factors `g = Ω(y)` for a cell point `y` over `Spec B`.

Since `Ω` is a monomorphism, the pullback of `y` to each `Spec B_𝔭` is the cell
point `(0, 1, z_𝔭)`. Hence each negative coordinate of `y`, and each torus
coordinate of `y` minus `1`, restricts to zero on `Spec B_𝔪` for every maximal ideal
`𝔪`. For a global function `a` on `Spec B`, write `a` as the image of an element of
`B` under the global-section isomorphism. The imported
`specMap_appTop_ΓSpecIso_inv` identifies its restriction to `Spec B_𝔪` with the
image of that element in `B_𝔪`. Mathlib's `eq_zero_of_localization` then shows
`a = 0`. Thus the negative coordinates of `y` vanish and its torus coordinate is
trivial, and `g = Ω(0, 1, posCoord y) = ∏ₖ u_{pos k}(posCoord y k)`.

**Root families.** As in the imported `exists_orderedProduct_eq_pos_of_isPos`, the
open immersion comes from the imported `LocalSplitBigCell.isOpenImmersion_cellMap`.
The equivariance comes from the root parametrizations, and the cocharacter from the
imported `exists_cocharacter_of_base`.

## Provenance and scope

The corresponding published result is Conrad's Theorem 5.1.13 (B. Conrad, *Reductive
group schemes*, in *Autour des schémas en groupes*, Panoramas et Synthèses 42–43,
2014). For a split reductive group over any nonempty scheme and a positive system of
roots, the multiplication map from the product of the positive root groups, in any
order, is an isomorphism onto a closed subgroup `U_{Φ⁺}`. The present module states
and proves only the consequence for points over affine test schemes: products of
positive root points have unique coordinates for the given enumeration `pos`. The
passage from local to arbitrary test rings is an explicit construction of this
module, by localization and openness of the big cell. The module does not prove
that the positive cell factor is a closed subgroup scheme. It provides no structure
constants for its group law, and it does not prove the local split Isomorphism
Theorem.
