# Legs and corners of locally realized actual gluing data

This internal helper module connects arrows of actual line bundles with their
underlying module maps. It also extracts leg and corner identities from
identities of restricted gluing-data arrows. Namespace:
`Langlands.AlgebraicGeometry.Picard.SquareGluingDescent`. The development is
internal; it follows no literature source. The notation is that of
`SquareGluingDescent` and `SquareGluingRespect`.

## Bridge to modules

An arrow `θ : M ⟶ M'` of the actual Picard groupoid of `X` is an isomorphism of
line bundles.

- `mh θ : M.of.obj ⟶ M'.of.obj` is its underlying map of `X`-modules, and
  `mi θ` is the underlying isomorphism of modules. `mi_hom` relates the two.
- `pic e` is the Picard-groupoid arrow given by an isomorphism `e` of the
  underlying modules. `mh_pic` says `mh (pic e) = e.hom`.
- `mh_comp` and `mh_map`: `mh` takes composition to composition and the
  pullback functor `P f` to `Scheme.Modules.pullback f`.
- `mh_injective`: `mh` is injective.
- `mh_sqH`: the underlying module map of the square comparison `sqH` is the
  published module square comparison `Langlands.Scheme.Modules.squarePullbackIso`.
  This is the published `SquareGluingFullyFaithful.squarePullbackIso_app`.

## Leg identities

- `sqH_nat` is naturality of the square comparison.
- `leg_of_eq`: on one pair of commuting maps `a₁ ≫ b₁ = a₂ ≫ b₂`, consider an
  identity between the two pulled-back arrows `x` and `y`. If it holds through
  the composition comparisons and the equality-induced arrows, then
  `(P a₁).map x ≫ sqH .. L' = sqH .. L ≫ (P a₂).map y`. The proof uses `sqH_eq`
  and cancellation of the composition comparisons.
- `CompI_inv_left`, `CompI_inv_right` and `R_obj_hom` record the legs of `CompI`
  and the specified overlap isomorphism of `c.R.obj E`.

## Corner and leg extraction

- `map_w`: let `Ψ : c.R.obj E ⟶ c.R.obj E'` be an arrow of restricted data
  whose legs are the restrictions of `l : E.left ⟶ E'.left` and
  `r : E.right ⟶ E'.right`. Then the corner square of `l` and `r` commutes after
  pullback along `c.g₀`. That square is
  `(P S.i₁).map l ≫ E'.hom = E.hom ≫ (P S.i₂).map r`. The proof uses the
  commutativity of `Ψ` in the comma category and naturality of the specified
  overlap isomorphisms, then cancels the two isomorphisms.
- `leg_left` and `leg_right`: take restricted arrows `Ψ₁` along `c` and `Ψ₂`
  along `c'` whose restrictions `pbH` to the overlap square `PB c c'` agree.
  Then their first legs, and their second legs, are compatible through the
  square comparison of the leg overlap. These are the compatibility hypotheses
  of module gluing over the leg covers.

## Compatibility of the induced local arrows

- `legs_compat_of`: let `N` be an actual line bundle on `S.X`, and let
  `ρ₁ : T.C.obj N₁ ≅ c.R.obj D` and `ρ₂ : T'.C.obj N₂ ≅ c'.R.obj D` be
  realizations. Let `σ₁ : (P c.t).obj N ⟶ N₁` and `σ₂ : (P c'.t).obj N ⟶ N₂` be
  local identifications. Suppose `τ` is an arrow respecting the realizations
  pulled back along cubes `a` and `b` with `comp a c = comp b c'`, and `τ` is
  compatible with `σ₁` and `σ₂` through the square comparison. Then the
  restrictions of `(cIi c N).inv ≫ T.C.map σ₁ ≫ ρ₁.hom` and of the analogous
  arrow for `c'` agree. The proof uses `pbH_phi`, the respect equation of `τ` and
  `cIi_congr`.
- `legs_compat` is `legs_compat_of` for the projection cubes `fstC c c'` and
  `sndC c c'` of the canonical overlap square.
