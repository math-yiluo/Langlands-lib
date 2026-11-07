# Isomorphisms of reductive groups over a reduced ring from big cells and field points

Module `Langlands.GroupScheme.Reductive.LocalSplitCellIsomorphism`, namespace
`Langlands.GroupScheme.LocalSplitCell`.

## Setting

`R` is a commutative ring and `G`, `H` are group schemes over `Spec R`. `T_I` is the coordinate
split torus. `Ga`, `rootPoint`, `orderedProduct`, `cellObj`, `cellPoint` and `cellMap` are as
in the Library module `Langlands.GroupScheme.Reductive.LocalSplitCell`. The big-cell map
`cellMap i u neg pos : 𝔾ₐᵐ × T_I × 𝔾ₐⁿ ⟶ G` sends `(v, t, w)` to
`(∏ₖ u_{neg k}(vₖ)) i(t) (∏ₖ u_{pos k}(wₖ))`.

## Definitions

- `cellUnit R I m n : 𝟙_ ⟶ cellObj R I m n`, the point `(0, 1, 0)`. It is built from the unit
  points of the three factors.
- `fieldPoint R K = (Over.map (algebraBaseMap R K)).obj (𝟙_ _)`: for an `R`-algebra `K`, the
  scheme `Spec K` as an object over `Spec R`.
- `precompPointsEquiv e G : G(Z') ≃* G(Z)`: precomposition with an isomorphism `e : Z ≅ Z'` of
  test objects, as an isomorphism of point groups.

## Results

- `orderedProduct_zero`: the ordered product of root points at `0` is `1`.
- `cellUnit_comp_cellMap`: `cellMap` sends `cellUnit` to the identity.
- `smooth_cellObj`: the cell source is smooth over `Spec R`.
- `isReduced_cellObj_tensor`: if `R` is reduced, the scheme underlying
  `cellObj R I m n ⊗ cellObj R I m n` is reduced.
- `nonempty_iso_of_fieldPoints`: let `R` be reduced and `G`, `H` reductive. Take torus maps
  `i`, `i'`, families `u`, `u'` of maps from `𝔾ₐ` and enumerations `neg`, `pos`, such that both
  `cellMap i u neg pos` and `cellMap i' u' neg pos` are open immersions. Suppose that for every
  field `K` (in universe `u`) and every morphism `s : Spec K ⟶ Spec R` there is an isomorphism
  `Ψ : G(s) ≃* H(s)` of the groups of points over `s`. Suppose `Ψ` sends `t ≫ i` to `t ≫ i'` for
  every torus point `t`, and `u_α(c)` to `u'_α(c)` for every `α` and every `c`. Then `G ≅ H`.
- `nonempty_iso_of_fieldAlgebras`: the same conclusion when the isomorphisms `Ψ` are supplied
  only over `fieldPoint R K` for fields `K` with an `R`-algebra structure.

## Proof

`cellUnit_comp_cellMap`: by the big-cell formula `comp_cellMap`, `cellUnit ≫ cellMap` is
`cellPoint` at the coordinates of `cellUnit`. The vector coordinates of a unit point are `0`
(coordinates are a group isomorphism), and its torus coordinate is `1`. Every root point at `0`
is `1` (`rootPoint_zero`) and `1 ≫ i = 1`.

`smooth_cellObj`: the vector groups are smooth (Library `Corepresented.smooth_groupScheme_iff`
for the polynomial algebra), the split torus is smooth (`smooth_splitTorus`), and products over
`Spec R` of smooth schemes are smooth (`GroupScheme.smooth_tensor`). `isReduced_cellObj_tensor`
applies `SmoothReducedBase.isReduced_of_smooth_of_isReduced` to the smooth structure map of the
product over the reduced scheme `Spec R`.

`nonempty_iso_of_fieldPoints` applies the Library's gluing theorem
`CellGluing.exists_iso_of_cellCompatible` to the two big-cell maps, with the common point
`cellUnit`. Its inputs are of three kinds.
- `G` and `H` are smooth with geometrically irreducible fibres: `IsReductive.smooth` and
  `IsReductive.geometricallyIrreducible`.
- `H` and `G` are separated over `Spec R`, being affine.
- The two compatibilities `CellCompatible j ν` and `CellCompatible ν j`. By
  `CellFieldCompatibility.cellCompatible_of_fieldCompatible` (the cell square is reduced) it
  suffices to check them at field points. There `cellRelation_of_map` (module
  `LocalSplitWeylFamily`) applies to `Ψ`, and to `Ψ.symm` for the reverse direction.

`nonempty_iso_of_fieldAlgebras`: given `s : Spec K ⟶ Spec R`, the ring map
`Spec.preimage s` makes `K` an `R`-algebra whose `algebraBaseMap` is `s`. The objects
`Over.mk s` and `fieldPoint R K` are then isomorphic by the identity of `Spec K`. Conjugating the
supplied `Ψ` by `precompPointsEquiv` gives the required isomorphism over `s`. Torus points and
root points move correctly under precomposition, by associativity and `comp_rootPoint`.

## Provenance

These are internal lemmas for the proof of the Isomorphism Theorem over a reduced local ring
(`LocalSplitReducedIsomorphismTheoremStatement`), written for this project. They combine the
Library's open-cell gluing (`CellGluing`) with the reduction of cell compatibility to field
points (`CellFieldCompatibility`). Reducedness of the base is what makes field points suffice.
The proofs follow no particular printed source.
