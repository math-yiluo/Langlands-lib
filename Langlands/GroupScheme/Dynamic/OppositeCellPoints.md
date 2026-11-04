# Points of the opposite cell in a dynamic parabolic quotient

This module is an internal helper for the proof of Conrad--Gabber--Prasad,
*Pseudo-reductive groups* (2nd ed., 2015), Proposition C.1.6, where the proof
works with the open cell `U_G(-λ) × P_G(λ)` of CGP Proposition 2.1.8(3). It
combines the Library's proved `oppositeCellStatement` (open immersion of the
multiplication `U_G(χ⁻¹) × P_G(χ) → G`) with `QuotientCell.isOpenImmersion`
(descent of that open immersion to a quotient). No other source is used.

Setting: `k` is a field and `G` an affine `k`-group with `Smooth G.X.hom`,
`IsAffineHom G.X.hom` and `IsAffine G.X.left`. `χ` is a cocharacter and
`opposite χ` is `t ↦ χ(t⁻¹)` (the composite with `Gm.powerHom (-1)`).
`cellMap χ` is the Library's closed subgroup
`Dynamic.Affine.unipotentHom (opposite χ)`, which represents `U_G(χ⁻¹)`.
`q : G.X ⟶ Q` is flat, surjective and quasi-compact, and `hf` says that
`g ≫ q = h ≫ q` iff `g⁻¹ * h ∈ P_G(χ)` on every test scheme.

- `isOpenImmersion_multiplication χ`: the multiplication
  `U_G(χ⁻¹) × P_G(χ) → G`, built from the Library's representing subgroups
  `Dynamic.Affine.unipotentHom` and `parabolicHom`, is an open immersion. This
  is `oppositeCellStatement`.
- `isOpenImmersion_cell χ q hf`: `cellMap χ ≫ q` is an open immersion. This is
  `QuotientCell.isOpenImmersion`; its fiber hypothesis uses that
  `Dynamic.Affine.parabolicHom χ` represents `P_G(χ)`.
- `cell χ q`: the set-theoretic image of `cellMap χ ≫ q` in `Q`. `isOpen_cell`
  says it is open.
- `exists_mem_unipotent χ q hf y hy`: a point `y : T ⟶ Q` whose underlying map
  lands in the cell is `u ≫ q` for some `u ∈ U_G(χ⁻¹)(T)`. The proof lifts `y`
  through the open immersion (`IsOpenImmersion.lift`) and composes with
  `cellMap χ`.
- `eq_of_mem_unipotent χ q hf hu hu' h`: points `u, u'` of `U_G(χ⁻¹)` with
  `u ≫ q = u' ≫ q` are equal. Both factor through `cellMap χ`, and
  `cellMap χ ≫ q` is a monomorphism.
- `range_subset_cell` and `range_one_subset_cell`: the image of any point of
  `U_G(χ⁻¹)`, in particular of the identity, lands in the cell.
