# Affine orbits of a smooth action relation: proof

Author: Worker 1420.

The theorem `Langlands.GroupScheme.SchemeAction.smoothActionAffineOrbit` has
type exactly `SmoothActionAffineOrbitStatement.{u}`. The statement is imported
unchanged from
[`SmoothActionAffineOrbitStatement`](SmoothActionAffineOrbitStatement.md).
The proof covers every field `k : Type u` and every universe `u`. It uses only
the hypotheses of the statement and adds no premise. It works over `k` itself,
with no algebraic closure, perfectness, Noetherian or reducedness argument. It
uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

Throughout, `Ψ = lift a.hom (snd G.X X) : G × X → X × X` is the action
relation `(g, y) ↦ (g • y, y)`. The hypothesis is that `Ψ.left` is smooth.

## Auxiliary morphisms (any base scheme `S`)

For a test object `T` and `t : T ⟶ X` in `Over S`:

- `actAlong t := (G.X ◁ t) ≫ a.hom : G × T → X`, that is `(g, s) ↦ g • t s`.
  The lemma `comp_actAlong` rewrites `f ≫ actAlong t` as
  `a.act (f ≫ fst) (f ≫ snd ≫ t)`.
- `relationAlong t := lift (actAlong t) (snd G.X T) : G × T → X × T`, that is
  `(g, s) ↦ (g • t s, s)`. By `relationAlong_fst`, composing it with the
  first projection `X × T → X` gives `actAlong t`.

## Step 1: base changes of `Ψ` are smooth

- `isPullback_relationAlong`: the square with `relationAlong t` on top,
  `G.X ◁ t` and `X ◁ t` as vertical maps, and `Ψ` at the bottom is a pullback
  in `Over S`. The lift of a cone `(u, v)` is
  `lift (v ≫ fst G.X X) (u ≫ snd X T)`. Each required equation is checked on
  the two product projections (`CartesianMonoidalCategory.hom_ext`).
- `isPullback_orbitMap`: for a rational section `x`, the square with
  `a.orbitMap x` on top, vertical maps `lift (𝟙 G.X) (toUnit G.X ≫ x)` and
  `lift (𝟙 X) (toUnit X ≫ x)`, and `Ψ` at the bottom is a pullback. The lift of
  a cone `(u, v)` is `v ≫ fst G.X X`. The equations use `comp_orbitMap`.
- `smooth_orbitMap` and `smooth_relationAlong`: `Over.forget S` maps both
  squares to pullback squares of schemes (`IsPullback.map`). Smoothness is
  stable under base change (`MorphismProperty.of_isPullback`), so
  `(a.orbitMap x).left` and `(relationAlong t).left` are smooth.

## Step 2: stability of the orbit (any base scheme `S`)

`mem_range_orbitMap_of_actAlong`: let `p` be a point of `G × T` such that
`(actAlong t).left p` lies in the image of `(a.orbitMap x).left`. Then
`t.left ((snd G.X T).left p)` also lies in that image.

The proof takes the scheme pullback `P` of `(actAlong t).left` and
`(a.orbitMap x).left`. By `Scheme.Pullback.exists_preimage_pullback` it has a
point `r` over `p`. The two projections give `f₁ : P ⟶ G × T` and
`f₂ : P ⟶ G` in `Over S` with `f₁ ≫ actAlong t = f₂ ≫ a.orbitMap x`. Let
`h = f₁ ≫ fst G.X T`. The group law of `P`-points gives
`(h⁻¹ * f₂) ≫ a.orbitMap x = f₁ ≫ snd G.X T ≫ t`, using `comp_orbitMap`,
`act_mul`, `comp_actAlong`, `inv_mul_cancel` and `act_one`. Evaluating this
equality at `r` shows that `(h⁻¹ * f₂).left r` is a preimage of `t s`.

## Step 3: open images and closed orbits over a field

Here `S = Spec k`.

- `isOpen_range_actAlong`: `(relationAlong t).left` is smooth (Step 1). Mathlib
  makes it universally open (`UniversallyOpen.of_flat`, since smooth morphisms
  are flat and locally of finite presentation). The projection
  `(fst X T).left = pullback.fst X.hom T.hom` is universally open by Mathlib's
  instance for morphisms to an integral scheme with one point, such as
  `Spec k`. Their composite `(actAlong t).left` is therefore universally open,
  so its image is open.
- `isClosed_range_orbitMap`: the complement of the image of
  `(a.orbitMap x).left` is open. Take `y` outside the image. Let
  `T = Spec κ(y)` with `t` the canonical morphism
  `X.left.fromSpecResidueField y`. Then `U = range (actAlong t).left` is open
  by the previous item. It contains `y`: the point `lift 1 (𝟙 T)` composed with
  `actAlong t` is `t`, and `t` sends the closed point to `y`. It misses the
  orbit: if `(actAlong t).left p` were in the orbit, Step 2 would put
  `t.left (snd p)` in the orbit. Every point of `Spec κ(y)` maps to `y`
  (`Scheme.fromSpecResidueField_apply`), so `y` would be in the orbit.

## Step 4: assembling the factorization

In `smoothActionAffineOrbit`, the image of the smooth morphism
`(a.orbitMap x).left` is open, since smooth morphisms are universally open. By
Step 3 it is also closed. Let `U : X.left.Opens` be this image and set:

- `Q = Over.mk (U.ι ≫ X.hom)` and `j = Over.homMk U.ι`.
- `qL = IsOpenImmersion.lift U.ι (a.orbitMap x).left`, with
  `qL ≫ U.ι = (a.orbitMap x).left` (`IsOpenImmersion.lift_fac`), and
  `q = Over.homMk qL`.

The required properties are proved as follows.

- `IsOpenImmersion j.left` holds because `U.ι` is an open immersion.
- `IsClosedImmersion j.left` holds by `IsClosedImmersion.of_isPreimmersion`,
  since the image of `U.ι` is `U`, which is closed.
- `IsAffineHom`, `LocallyOfFiniteType` and `QuasiCompact` for
  `Q.hom = U.ι ≫ X.hom` follow from instances. A closed immersion is affine,
  quasi-compact and of finite type. `X.hom` is affine (hence quasi-compact) and
  locally of finite type, and each property is stable under composition.
- `Smooth q.left`: the square with top `𝟙 G`, left `qL`, right
  `(a.orbitMap x).left` and bottom `U.ι` is a pullback by
  `IsPullback.of_horiz_isIso_mono`, because `U.ι` is a monomorphism. So `qL`
  is a base change of the smooth orbit morphism.
- `Surjective q.left`: a point `u` of `U` maps under `U.ι` to some
  `(a.orbitMap x).left g`. Then `qL g = u`, by injectivity of `U.ι`
  (`Scheme.Hom.isOpenEmbedding`) and `qL ≫ U.ι = (a.orbitMap x).left`.
- `QuasiCompact q.left` holds by instance: `G.X.left` is affine because
  `G.X.hom` is an affine morphism to an affine scheme. `U` is affine as a
  closed subscheme of the affine scheme `X.left`. A morphism between affine
  schemes is quasi-compact.
- `q ≫ j = a.orbitMap x` is `Over.OverMorphism.ext` applied to `lift_fac`.

## Relation to the literature

The statement isolates the orbit argument in Conrad–Gabber–Prasad,
*Pseudo-reductive groups*, 2nd edition (2015), proof of Proposition A.8.12,
printed p.554 (PDF p.580), registered as
`conrad-gabber-prasad-2015-pseudo-reductive`. The book first reduces to an
algebraically closed field (printed p.552). It obtains smooth orbit maps by
base change of the action map and concludes that orbits are open and pairwise
disjoint. The Lean proof does not reduce to an algebraically closed field.
Closedness of a rational orbit comes from Step 3 over `k`: the open set
`U` built from `Spec κ(y)` contains `y` and misses the orbit. The group-law
stability argument of Step 2 replaces the book's partition of the geometric
scheme into orbits.
