# Matrix coefficients against a covector as an embedding into a regular representation

For a representation `ρ` of an affine group `G` over a field and a covector `ξ`, the
matrix coefficients `v ↦ matrixCoefficient G ρ ξ v` (module
`Reductive.EigenMatrixCoefficient`) are coordinates of `G`. This module shows that,
for irreducible `ρ` and nonzero `ξ`, they identify `ρ` with an actual finite regular
representation `affineRegularRepresentation G V b hV` (module
`Reductive.CovariantRegularFixedLine`). It also identifies the coordinate function of
the image of `v` with the matrix coefficient of `v`.

## Intertwiners into a regular representation are matrix coefficients

`Chevalley.affineRegularCoordinateMap_mulVec_eq_matrixCoefficient`. Let `V` be a
finite subspace of the coordinate algebra, stable under every right action
`rightAct ψ`, with basis `b`. Let `C` intertwine `ρ` with
`affineRegularRepresentation G V b hV`. Then for every `v`,

```text
affineRegularCoordinateMap G V b (C *ᵥ v) = matrixCoefficient G ρ ξ_C v,
```

where `ξ_C = (fun i => counit (b i)) ᵥ* C`.

Proof. Two coordinates are equal when they agree at every point of every scheme test
(`ext_pointAlgebraHom`). At a point `g`, the multiplication formula
`pointAlgebraHom_affineRegularCoordinateMap_mul` with `g = 1 * g` expresses the
left-hand side as `(counit ∘ b) ⬝ᵥ (σ(g) (C v))`, where `σ` is the regular
representation; the identity point evaluates by the counit
(`pointAlgebraHom_one_apply`). The intertwining equation `σ(g) C = C ρ(g)` turns this
into `((counit ∘ b) ᵥ* C) ⬝ᵥ (ρ(g) v)`. That is the value of the matrix coefficient
(`pointAlgebraHom_matrixCoefficient`).

## The bijective embedding

`Chevalley.exists_affineRegular_bijective_matrixCoefficient`: for irreducible `ρ`
and `ξ ≠ 0`, there are `V`, `d`, a basis `b : Basis (Fin d) k V`, the stability proof
`hV` and a matrix `C` such that:

- `C` intertwines `ρ` with `affineRegularRepresentation G V b hV`;
- `C.mulVecLin` is bijective;
- `affineRegularCoordinateMap G V b (C *ᵥ v) = matrixCoefficient G ρ ξ v` for every
  `v`.

Proof. Let `N` be the universal matrix of `ρ`
(`Unipotent.universalMatrix` of the restriction of `ρ` along `groupSchemeIso G`), and
let `a j = ∑ i, ξ i • N i j`. These are the matrix coefficients of `ξ` against the
basis vectors.

- The coalgebra identities of the universal matrix give
  `Δ (a j) = ∑ l, a l ⊗ N l j` (`Unipotent.comul_universalMatrix`) and
  `counit (a j) = ξ j` (`Unipotent.counit_universalMatrix`).
- `V` is the span of the `a j`. The comultiplication formula shows that `V` is stable
  under every `rightAct ψ`. `V` is finite-dimensional and `b` is `Module.finBasis`.
- `C` is `coactionCoordinates V b a`, the coordinates of the `a j` in the basis `b`.
  It intertwines the corepresented restriction of `ρ` with the regular
  representation, by `intertwines_of_universalMatrix`,
  `regularRepresentation_universalMatrix` and `coactionCoordinates_mul`. Restricting
  back along `(groupSchemeIso G).inv` gives the intertwiner from `ρ`.
- Expanding in the basis gives `affineRegularCoordinateMap G V b (C *ᵥ c) = ∑ j, c j • a j`.
- The counits of the basis, multiplied by `C`, give back `ξ`. So the first lemma
  identifies the coordinate of `C *ᵥ v` with the matrix coefficient of `ξ`.
- Injectivity. `C` is a nonzero intertwiner from an irreducible representation
  (`Intertwines.injective_of_isIrreducible`). If `C` were zero, every `a j` would
  vanish, so `ξ j = counit (a j) = 0` for all `j`, contradicting `ξ ≠ 0`.
- Surjectivity. Every coordinate vector `x` gives an element
  `affineRegularCoordinateMap G V b x` of `V`, which is a combination `∑ j, c j • a j`.
  Since the coordinate map is injective, `C *ᵥ c = x`.

## Provenance

This is internal: a one-covector form of the standard embedding of a representation
into the regular representation by matrix coefficients. One covector suffices here
because `ρ` is irreducible.
