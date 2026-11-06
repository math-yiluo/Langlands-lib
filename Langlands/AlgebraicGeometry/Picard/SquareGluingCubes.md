# Commuting cubes between commuting squares of schemes

This internal helper module provides the pure scheme geometry used by the
proof of `FieldPicardInfinitesimalGluingStatement`. It mentions no line
bundles or Picard groupoids. All of its declarations live in the namespace
`Langlands.AlgebraicGeometry.Picard.SquareGluingDescent`. The development is
internal; it follows no literature source.

## Squares and cubes

- `Sq` is a structure for a commuting square of schemes in one universe `u`.
  It has a corner `X₀`, two legs `X₁` and `X₂`, a total scheme `X`, maps
  `i₁ : X₀ ⟶ X₁`, `i₂ : X₀ ⟶ X₂`, `j₁ : X₁ ⟶ X`, `j₂ : X₂ ⟶ X`, and the
  equation `w : i₁ ≫ j₁ = i₂ ≫ j₂`. `Sq.w_assoc` is its reassociated form.
- `CubeMap S T` is a commuting cube *from* the square `T` *to* the square `S`.
  It has four maps `t : T.X ⟶ S.X`, `g₁ : T.X₁ ⟶ S.X₁`, `g₂ : T.X₂ ⟶ S.X₂` and
  `g₀ : T.X₀ ⟶ S.X₀`, together with the four face equations
  `h₁ : T.j₁ ≫ t = g₁ ≫ S.j₁`, `h₂ : T.j₂ ≫ t = g₂ ≫ S.j₂`,
  `k₁ : T.i₁ ≫ g₁ = g₀ ≫ S.i₁` and `k₂ : T.i₂ ≫ g₂ = g₀ ≫ S.i₂`.
- `CubeMap.ext'` says that a cube is determined by its four maps.
- `CubeMap.comp c' c` composes `c' : CubeMap T T'` with `c : CubeMap S T` to
  give a cube from `T'` to `S`, componentwise. `CubeMap.comp_assoc` is its
  associativity.

## Cartesian cubes

`CubeMap.Cart c` holds when three faces are pullback squares: the two leg faces
`IsPullback c.g₁ T.j₁ S.j₁ c.t` and `IsPullback c.g₂ T.j₂ S.j₂ c.t`, and the
first corner face `IsPullback c.g₀ T.i₁ S.i₁ c.g₁`.

- `Cart.comp`: composites of cartesian cubes are cartesian (horizontal pasting).
- `Cart.isOpenImmersion_g₁`, `Cart.isOpenImmersion_g₂`, `Cart.isOpenImmersion_g₀`:
  if `c` is cartesian and `c.t` is an open immersion, then so are `c.g₁`, `c.g₂`
  and `c.g₀`, because open immersions are stable under base change.
- `isPullback_exists_preimage`: in a pullback square of schemes, any two points
  with the same image in the base come from one point of the pullback. It
  transports the published `Scheme.Pullback.exists_preimage_pullback` along
  `IsPullback.isoPullback`.

## Overlap squares

Fix two cubes `c : CubeMap S T` and `c' : CubeMap S T'` into one square.

- `PB c c'` is the overlap square. Each of its four corners is the scheme
  pullback of the corresponding components of `c` and `c'`, for example
  `X := pullback c.t c'.t` and `X₁ := pullback c.g₁ c'.g₁`. Its maps are the
  induced `pullback.map`s. The declaration is reducible, so these corners are
  the literal Mathlib pullbacks.
- `fstC c c' : CubeMap T (PB c c')` and `sndC c c' : CubeMap T' (PB c c')` are
  the two projection cubes. `fstC_comp` says
  `comp (fstC c c') c = comp (sndC c c') c'`.
- `cart_fstC`: if `c'` is cartesian, then `fstC c c'` is cartesian.
  `cart_sndC`: if `c` is cartesian, then `sndC c c'` is cartesian. Both are proved
  by vertical pasting with the pullback squares defining `PB c c'`.
- `comp_eq_t`, `comp_eq_g₁`, `comp_eq_g₂` and `comp_eq_g₀` extract the component
  equations from an equation of composite cubes `comp a c = comp b c'`.
- `PB.lift a b e` is the cube into the overlap square induced by two cubes
  `a : CubeMap T W` and `b : CubeMap T' W` with `comp a c = comp b c'`. Its
  components are `pullback.lift`s. `PB.lift_fstC` and `PB.lift_sndC` give its two
  composites.
