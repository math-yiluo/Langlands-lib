# The translated big-cell charts and the torus characters in the function field

This internal helper module, used in the proof of
`SplitSimplyConnectedFactorialStatement`, defines for each simple root `a` the
big-cell chart translated by `u_a(1)`. It compares a torus character read on the
two charts.

## Left translations

For a group scheme `G` over `S` and a point `g : 𝟙_ (Over S) ⟶ G.X`:

- `leftTranslation g : G.X ⟶ G.X` is `x ↦ g · x`; on points,
  `comp_leftTranslation` gives `x ≫ leftTranslation g = g · x`;
- `isIso_leftTranslation`: it is an isomorphism, with inverse the translation by
  `g⁻¹`.

`nonempty_cellSpec` records that the cell spectrum is nonempty.

## The translated chart

For `D : CellData k G`, enumerations `neg`, `pos` of the negative and positive
roots, and a root `a`:

- `tchart a` is `chart neg pos` followed by left translation by `u_a(1)`. On
  points, `comp_tchart` gives `z ≫ tchart a = u_a(1) · (z ≫ chart)`.
  It is an open immersion (`isOpenImmersion_tchart`).

## The boundary localization

For a simple root `a`:

- `oppIndex ha` is the position of `-a` among the negative roots;
  `boundaryRing n neg ha = 1 + v_{oppIndex}` is the boundary function
  `1 + y_{-a}` in `CellRing`.
- `BoundaryLoc` is the localization away from `1 + y_{-a}`. `boundarySpec` is its
  spectrum over `Spec k`, which is nonempty (`nonempty_boundarySpec`, since
  `1 + y_{-a}` is prime and hence nonzero). `boundaryIncl` is the open immersion
  into the cell spectrum (`isOpenImmersion_boundaryIncl`, `pointRing_boundaryIncl`).
- `boundaryUnit` is `1 + y_{-a}` as a unit on `boundarySpec`
  (`boundaryUnit_val`).
- `exists_boundary_comparison`: there is `ψ : boundarySpec ⟶ cellSpec` with
  `ψ ≫ chart = boundaryIncl ≫ tchart a`, and the torus coordinate of `ψ` is
  `a∨(1 + y_{-a})` times that of `boundaryIncl`. This is
  `exists_translate_cellPoint` (module `FactorialRankOne`) with `e₀ = 1`, applied
  to the universal point of `boundarySpec`, followed by the isomorphism
  `cellCoordHom`.

## Torus characters on the charts

- `charUnit m n χ = ∏ᵢ tᵢ ^ χᵢ` is the torus character `χ : I → ℤ` as a unit of
  `CellRing`. `charSection m n χ` and `boundarySection n neg ha` are the
  corresponding global functions on the cell spectrum.
- `unitsMap_pointRing_charUnit`: the value of `charUnit χ` at a point `z` is the
  product of the `χᵢ`-th powers of the torus coordinates of `z`.
- `toFunctionField_charSection` (for `G.X.left` integral): in the function field
  of `G`,

  ```
  toFunctionField chart (charSection χ)
    = toFunctionField (tchart a) (charSection χ)
      · toFunctionField (tchart a) (boundarySection) ^ ⟨χ, a∨⟩
  ```

  where `⟨χ, a∨⟩ = coPairing χ (P.coroot a)`. The proof pulls both sides back to
  `boundarySpec` by `exists_boundary_comparison` and uses
  `toFunctionField_comp` (module `FunctionFieldChart`).

Provenance: internal. This is the chart comparison of step 5 of the route
suggested in the task context (a character `t^λ` equals a unit times
`Y^{⟨λ, a∨⟩}` on the boundary chart), with the translate `u_a(1) · Ω` instead of
`n_a · Ω`.
