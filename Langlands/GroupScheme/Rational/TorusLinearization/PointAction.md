# Abstract torus actions on affine space

Helper module for the proof of `TorusVectorActionLinearizationStatement` (task 3be1ce22).
Internal machinery only.

`PointAction k K I n` packages the functor-of-points data of a torus over a field `k` acting on
`n`-dimensional affine space by additive maps:

- `Pt B` gives the points with values in a `k`-algebra `B`, with transport `map` along
  `k`-algebra maps, satisfying functoriality (`map_id`, `map_comp`);
- `act t : (Fin n → B) → (Fin n → B)` is the action of a point `t`; it is additive (`act_add`)
  and natural (`act_map`);
- `σ` is the splitting over a field extension `K`: over `K`-algebras `C`, families of units
  `I → Cˣ` give points. `σ` is surjective, natural for `K`-algebra maps (`map_σ`) and
  multiplicative for the action (`act_σ_one`, `act_σ_mul`).

The structure has no group law on points, and `K/k` may be any field extension.

Derived notions:
- `poly t` is the action of `t` on the generic point `X` of `n`-space over `B[X]`, so
  `act t x = aeval x (poly t)` (`act_eq_aeval`). `poly` is natural in `B` (`poly_map`), and its
  entries are additive polynomials (`isAddPoly_poly`).
- `pull t := aeval (poly t)` pulls polynomials over `k` back along the action of `t`, and
  `aeval_pull` records this.
