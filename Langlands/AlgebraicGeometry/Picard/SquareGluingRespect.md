# Arrows respecting realizations of restricted actual gluing data

This internal helper module adds a predicate for arrows of actual line bundles
that respect realizations of restricted gluing data. It also proves the closure
properties that the Čech cocycle argument needs. Namespace:
`Langlands.AlgebraicGeometry.Picard.SquareGluingDescent`. The development is
internal; it follows no literature source. The notation (`Sq`, `CubeMap`, `R`,
`C`, `pb`, `pcH`, `pcI`, `sqH`) is that of `SquareGluingDescent`.

## The square comparison through composition comparisons

`sqH_eq` unfolds the published `PicardGroupoid.squarePullbackIso`. The
square comparison `sqH i₁ i₂ j₁ j₂ w L` is
`pcH i₁ j₁ L ≫ eqToHom _ ≫ pcI i₂ j₂ L`, where the middle arrow is induced by
`w : i₁ ≫ j₁ = i₂ ≫ j₂`.

## The predicate `Resp`

Fix `D : S.GD` and two cubes `c c' : CubeMap S T`. Let
`σ : T.C.obj M ≅ c.R.obj D` and `σ' : T.C.obj M' ≅ c'.R.obj D` be realizations.
An arrow `θ : M ⟶ M'` satisfies `Resp θ σ σ'` when `c = c'` and
`T.C.map θ ≫ σ'.hom` equals `σ.hom` followed by the equality-induced arrow for
`c = c'`. Allowing two propositionally equal cubes lets realizations along
cubes that are equal but not definitionally equal be compared.

- `Resp.of_eq`, `Resp.of_eq'` and `Resp.eq` translate between `Resp` and plain
  equations.
- `Resp.comp` and `Resp.symm` close `Resp` under composition and under inverses
  of isomorphisms.
- `Resp.unique`: if `T.C` is faithful, at most one arrow respects two given
  realizations.
- `Resp.along`: pulling back along a further cube `d` preserves `Resp`, with
  `pb` applied to both realizations (from `pb_respects`).

## Respect of the coherence arrows

- `resp_pcH` and `resp_pcI`: the composition comparison and its inverse
  respect a twice pulled-back realization and the once pulled-back realization
  along the composite cube (from `pb_pb`).
- `resp_eqToHom`: the arrow induced by an equality of cubes respects the two
  pullbacks.
- `resp_sqH`: for two factorizations `comp e₁ d₁ = comp e₂ d₂` of one cube, the
  square comparison respects the two successive pullbacks. It is the composite
  of `resp_pcH`, `resp_eqToHom` and `resp_pcI`, via `sqH_eq`.

## Pulling back arrows between restrictions

- `pbH c e Ψ` restricts an arrow `Ψ : c.R.obj E ⟶ c.R.obj E'` along a further
  cube `e`, conjugated by the composition isomorphisms `CompI`.
- `cIi_comp_inv` solves `cI_comp` for the inner comparison.
- `pbH_phi` computes `pbH` on an arrow of the form
  `(cIi c L).inv ≫ T.C.map σ ≫ ρ.hom`. The result is the arrow of the same form
  along the composite cube, built from `pcI e.t c.t L ≫ (P e.t).map σ` and the
  pulled-back realization `pb c e ρ`.
- `cIi_congr` relates the comparisons of two equal cubes through
  equality-induced arrows.
