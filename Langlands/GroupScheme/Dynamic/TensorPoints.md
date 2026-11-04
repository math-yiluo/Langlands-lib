# Base change of points along `Spec Ω → Spec k`

This module is an internal helper for the proof of Conrad--Gabber--Prasad,
*Pseudo-reductive groups* (2nd ed., 2015), Proposition C.1.6. It handles the
base change to an algebraic closure `Ω` of the points used in that proof. It
uses only the pullback adjunction `Over.mapPullbackAdj` and the Library's
pullback point equivalence.

`k` is a field, `Ω` a field with `Algebra k Ω`, and `scalarMap k Ω` the map
`Spec Ω → Spec k`.

- `pullbackPoint z`: for a `k`-scheme `Y` and an `Ω`-algebra `A`, a point
  `z : Spec A ⟶ Y` over `k` gives a point of `Y_Ω` over `Spec A`, by the
  adjunction. `pullbackPoint_comp` gives naturality in `Y`.
- `tensorPoint Ω z`: for a `k`-algebra `K` and `z : Spec K ⟶ Y`, the point
  `pullbackPoint (Spec (K → Ω ⊗[k] K) ≫ z)` of `Y_Ω` over `Ω ⊗[k] K`.
  `tensorPoint_comp` gives naturality in `Y`.
- For a corepresented group `G = Spec B`:
  - `tensorGPoint Ω z`, the base change `bcPoint (includeRight ∘ z)` of a
    `K`-point, typed as a point of the group `G_Ω`;
  - `tensorGPoint_eq`, which writes it through the pullback point equivalence;
  - `tensorPoint_eq_tensorGPoint`, which says it agrees with `tensorPoint`;
  - `tensorGPoint_mul`, which says it is multiplicative, because the pullback
    point equivalence is.
- `tensorGPoint_mem_unipotent ν hz`: base change carries `U_G(ν)` into
  `U_{G_Ω}(ν_Ω)`. This combines the Library's `unipotent_baseChange` with
  stability of subgroup functors under restriction.
- `algOverHom_comp_ofAlgHom_ofId` and `tensorGPoint_ofAlgHom_ofId`: restricting
  or base-changing the constant point of a `k`-point `a` gives the constant
  point of `a`.
