# Characteristic powers on rank-one open cells

This derived supporting construction works over an arbitrary field `k : Type u`.
It uses the published `RootCell.IsRootCell` interface and open-cell gluing theorem.
The two commutative torus objects need not be identified. The hypotheses for the
cell construction are an actual morphism `t : T → T′`, a characteristic exponent
`p` (`ExpChar k p`), an integer `e ≥ 0`, and characters and cocharacters satisfying

- `t ≫ χ′ = p^e • χ`, and
- `χv ≫ t = p^e • χv′`.

The additive-line scheme map `gaPower q` is defined by the coordinate `X ↦ X^q`.
The coordinate lemmas characterize this map on every test scheme, reusing
`crd_injective` from the shared `SplitRankOneRootCellReduction` module. For
characteristic powers, `gaPower_mul` and `gaPower_one` show that its action on
points preserves the group operation and identity. To prove additivity on all
test schemes, `add_pow_sections` treats a subsingleton ring of global sections
separately; otherwise the injective field algebra map transfers the characteristic
exponent, and Mathlib's characteristic-power binomial identity applies.

Character evaluation turns natural multiples into ordinary powers.
`gaPower_weight` therefore intertwines the two torus actions under the character
equation. The cocharacter equation similarly gives `coU_comp_of_coroot`: the
source torus factor at a unit `u` maps to the target cocharacter at `u^(p^e)`.
`pow_unit_eq` raises the rank-one relation's unit equation to the same power,
and `pt_unit_mul_comp_gaPower` handles its reciprocal unit factors.

The map `powerCell t q` raises both additive coordinates to the power `q` and
applies `t` to the middle torus coordinate. `cellProd_powerCell` proves that it
intertwines the explicit source and target rank-one multiplication formulas.
Given source and target `IsRootCell` data, `powerCell_compatible` converts an
arbitrary relation between source cell points into the explicit product formula,
using the source open immersion to identify the product's cell coordinates.
The corresponding target formula then proves the same relation after applying
the power-cell map.

Finally, `exists_powerHom` assumes that the source group is connected reductive
and that both groups have the stated root-cell data. The source is smooth with
geometrically integral fibres. `CellGluing.glueHom` extends the compatible cell
map to an actual group-scheme homomorphism `φ : G → G′`. The conclusion specifies
its entire restriction to the cell, the torus square `i ≫ φ = groupHom t ≫ i′`,
and its positive and negative root maps, which are the target root maps
precomposed with `gaPower (p^e)`. These restrictions follow by composing the cell
identity with its torus and additive axes. Target connected reductivity and
splitness of either torus are not extra hypotheses of this derived result.

Provenance is derived: this is an algebraic compatibility calculation and an
application of the published rank-one cell and gluing interfaces, together with
Mathlib's characteristic-power identities. It does not assert that the glued
homomorphism is finite, flat, or surjective. It supplies a local homomorphism
construction for the general split-isogeny task; it does not by itself prove the
general realization or fixed-torus extension theorem.
