# Descent calculus for actual Picard square gluing data

This internal helper module sets up the coherence calculus used in the Čech
gluing step of the proof of `FieldPicardInfinitesimalGluingStatement`. It works
with actual line bundles, their actual isomorphisms, and the published coherent
comparison isomorphisms of ordinary pullback. Namespace:
`Langlands.AlgebraicGeometry.Picard.SquareGluingDescent`. The development is
internal; it follows no literature source.

## Pullback comparisons on one leg

- `P f` abbreviates the published `PicardGroupoid.pullback f`.
- `pcH f g L` and `pcI f g L` are the components at `L` of the published
  composition comparison `PicardGroupoid.pullbackComp f g` and of its inverse.
  They are written with nested source or target `(P f).obj ((P g).obj L)`.
  `pcI_pcH` and `pcH_pcI` say that the two are inverse. `pcH_nat` is naturality.
- `sqH i₁ i₂ j₁ j₂ w L` is the component of the published square comparison
  `PicardGroupoid.squarePullbackIso i₁ i₂ j₁ j₂ w`.
- `pc_assoc` restates the published `PicardGroupoid.pullback_associativity` at
  one bundle: `(P f).map (pcH g h L) ≫ pcH f (g ≫ h) L` equals
  `pcH f g _ ≫ pcH (f ≫ g) h L` followed by the equality-induced arrow for
  `(f ≫ g) ≫ h = f ≫ (g ≫ h)`.
- `paste_leg` solves the published
  `SquareGluingRestrictionComposition.square_paste` for the square comparison of
  a pasted square. That comparison is the composite of an inverse composition
  comparison, the two square comparisons and a composition comparison.

## Gluing data of a square and restriction along a cube

For `S : Sq`:

- `S.GD` is the published groupoid `PicardGroupoid.SquareGluingData S.i₁ S.i₂`.
  Its objects are actual line bundles on the two legs with a specified
  isomorphism of their pullbacks to the corner.
- `S.C` is the published comparison functor
  `PicardGroupoid.squareGluingComparison S.i₁ S.i₂ S.j₁ S.j₂ S.w`.

For a cube `c : CubeMap S T`:

- `c.R : S.GD ⥤ T.GD` is the published restriction
  `SquareGluingRestriction.pullback` along the leg maps `c.g₁`, `c.g₂` and the
  corner map `c.g₀`. The `@[simp]` lemmas `R_map_left`, `R_map_right`,
  `R_obj_left` and `R_obj_right` record that its legs are ordinary pullbacks.
- `c.cI : PicardGroupoid.pullback c.t ⋙ T.C ≅ S.C ⋙ c.R` is the published
  comparison `SquareGluingRestrictionComparison.comparisonIso`. `cIa` is its
  component with a clean type and `cIi` the corresponding isomorphism.
  `cI_hom_app_left`, `cI_hom_app_right`, `cIa_left` and `cIa_right` identify
  its legs with square comparisons.
- `Comp c c' : c.R ⋙ c'.R ≅ (comp c' c).R` is the published composition
  `SquareGluingRestrictionComposition.pullbackComp` of restrictions, with
  components `CompA` and `CompI`. Its legs are composition comparisons
  (`Comp_hom_app_left`, `Comp_hom_app_right`, `CompA_left`, `CompA_right`).
- `C_map_left` and `C_map_right` give the legs of `T.C.map`.

The main coherence results are:

- `cI_comp` (pseudonaturality): `cIa (comp c' c) L` is the composite of
  `T'.C.map (pcI c'.t c.t L)`, `cIa c' ((P c.t).obj L)`, `c'.R.map (cIa c L)` and
  `CompA c c' (S.C.obj L)`. Each leg is an instance of `paste_leg`.
- `CompA_nat` and `cIa_nat` are naturality of `Comp` and `cI`.
- `Comp_assoc` is associativity of `Comp` for three cubes, up to the
  equality-induced arrow for `CubeMap.comp_assoc`. Each leg is `pc_assoc`.

## Pulling back realizations

A realization of a restricted datum is an isomorphism
`ρ : T.C.obj N ≅ c.R.obj D` in `T.GD`, with `D : S.GD` and `N` an actual line
bundle on `T.X`.

- `pb c c' ρ : T'.C.obj ((P c'.t).obj N) ≅ (comp c' c).R.obj D` pulls `ρ` back
  along a further cube `c' : CubeMap T T'`. It is the composite
  `cIi c' N ≪≫ c'.R.mapIso ρ ≪≫ CompI c c' D`, and `pb_hom` gives its `hom`.
- `pb_respects`: an arrow `τ : N₁ ⟶ N₂` with `T.C.map τ ≫ ρ₂.hom = ρ₁.hom` keeps
  this property after pulling back along `c'`.
- `pb_pb`: pulling back twice agrees with one pullback along the composite cube.
  The two differ by the composition comparison `pcH` on the bundle and the
  equality-induced arrow for `CubeMap.comp_assoc`. The proof combines
  `cI_comp`, `CompA_nat` and `Comp_assoc`.
