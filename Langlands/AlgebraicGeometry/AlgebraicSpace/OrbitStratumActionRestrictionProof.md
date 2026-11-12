# Proof that smooth group actions restrict to reduced orbit-dimension strata

Author: Worker 4665.

`orbitStratumActionRestriction` proves
`Langlands.AlgebraicGeometry.AlgebraicSpace.OrbitStratumActionRestrictionStatement.{u}`
from the published statement module `OrbitStratumActionRestrictionStatement`, for an
arbitrary universe `u`. Over a field `k`, a group scheme `G` smooth over `k` acts by
`a` on a scheme `V` locally of finite type over `k`, and `i : Z ⟶ V` is an immersion
from a reduced scheme whose image is the set of points of orbit dimension `d`. The theorem
gives an action `b` of `G` on `Z` with `b.hom ≫ i = (G.X ◁ i) ≫ a.hom`. It also shows that
every action with this property has orbit dimension `d` at every point of `Z`.

The proof follows the derivation in the statement's Markdown, with one change. Instead of
choosing points of `G` over residue fields, it compares the stabilizer schemes through two
cartesian squares of schemes over `Spec k`. Fibre dimensions are then compared by a
general base-change lemma. The helper declarations are in the namespace
`Langlands.AlgebraicGeometry.AlgebraicSpace.OrbitStratumActionRestriction`.

## Fibre dimension under base change

`topologicalKrullDim_fiber_of_isPullback` considers a cartesian square with
`a : P ⟶ X`, `b : P ⟶ Y`, `f : X ⟶ W` and `g : Y ⟶ W`, where `f` is locally of finite
type. For every point `y` of `Y`, the fibre of `b` over `y` has the same topological Krull
dimension as the fibre of `f` over `g y`. The published `fiberBaseChangeSquare`
(`SchemeFiberBaseChange`) shows that the fibre of `b` is the base change of the fibre of
`f` along `Spec κ(y) ⟶ Spec κ(g y)`. The structure map of the fibre of `f` is locally of
finite type by base change. The comparison map `fiberBaseChangeMap` is surjective because
`Spec κ(y) ⟶ Spec κ(g y)` is surjective (the target is a point) and surjectivity is stable
under base change. Both dimensions are suprema of local dimensions
(`topologicalKrullDim_eq_iSup_at`). The local dimensions agree pointwise by the published
`topologicalKrullDimAt_isPullback_fieldExtension` (`SchemeLocalDimensionBaseChangeProof`).
Surjectivity then identifies the two suprema.

## The stabilizer scheme

`stab a` is the pullback of `(a, snd) : G × V ⟶ V × V` along the diagonal of `V`. Its
projection `stabπ a : stab a ⟶ V` is the morphism whose fibres appear in
`HasOrbitDimension`, so `hasOrbitDimension_iff` holds by definition. `stabG a` is the
projection to `G`. `act_stab` states that the universal point `(stabG a, stabπ a)` of the
stabilizer satisfies `stabG a · stabπ a = stabπ a`. `stabMk` builds a `T`-point of the
stabilizer from points `h` of `G` and `v` of `V` with `h · v = v`. `stab_hom_ext` states
that a point of the stabilizer is determined by its two projections.
`locallyOfFiniteType_stabπ` shows that `stabπ a` is locally of finite type when `G` is
locally of finite type over the base. The morphism `(a, snd)` is locally of finite type
because its composite with the second projection `V × V ⟶ V` is the base change
`snd : G × V ⟶ V`. Then `stabπ a` is its base change along the diagonal, through the
forgetful functor `Over S ⥤ Scheme`, which preserves pullbacks.

## Equivariant monomorphisms

Let `b` be an action on `Z` and `i : Z ⟶ V` a monomorphism with
`b.hom ≫ i = (G.X ◁ i) ≫ a.hom`. Then `act_comp_of_equivariant` gives
`(h · z) ≫ i = h · (z ≫ i)` on points. `stabMap` sends the stabilizer of `b` to the
stabilizer of `a` by `(h, z) ↦ (h, i z)`. `isPullback_stabMap` shows that the square with
sides `stabMap`, `stabπ b`, `stabπ a` and `i` is cartesian. A point `(h, v)` of `stab a`
with `v = z ≫ i` gives `(h, z)` in `stab b`: we have `(h · z) ≫ i = h · v = v = z ≫ i`,
so `h · z = z` because `i` is a monomorphism. With the base-change lemma, this gives
`hasOrbitDimension_iff_of_equivariant`: `HasOrbitDimension b z d` holds if and only if
`HasOrbitDimension a (i z) d` holds. The statement's derivation instead uses
`κ(z) = κ(i z)`. The implemented proof does not need this, because the base-change lemma
applies to any cartesian square.

## Conjugation

`conjMap a` maps the pullback of `stabπ a` along `snd : G × V ⟶ V` to `stab a` by
`(h, (g, v)) ↦ (g h g⁻¹, g · v)`, where `h · v = v`. `conjInv` is its inverse on points:
it sends a point `x` of `stab a` and a point `(g, v)` of `G × V` with
`stabπ a x = g · v` to `(g⁻¹ h g, (g, v))`, where `h = stabG a x`. The group identities in
the point group `T ⟶ G` are proved with `MonObj.comp_mul`, `GrpObj.comp_inv` and the
`group` tactic. `isPullback_conjMap` shows that the square with sides `conjMap a`,
`pullback.snd`, `stabπ a` and `a.hom` is cartesian. So both `a.hom` and `snd` pull the
stabilizer back to the same scheme over `G × V`. For a point `q` of `G × V`, the
base-change lemma applied to this square and to the defining pullback square of `snd` gives
`hasOrbitDimension_act_iff`. The orbit dimension at `a.hom q` equals the orbit dimension at
`snd q`.

## Factoring through an immersion

`exists_lift_of_isImmersion` considers an immersion `i : X ⟶ Y` and a morphism
`f : T ⟶ Y` from a reduced scheme whose set-theoretic image lies in the image of `i`. It
shows that `f` factors through `i`. The image of `f` lies in the open subscheme
`i.coborderRange`, so `f` lifts to a morphism `f'` into it (`IsOpenImmersion.lift`). Inside
this open, `i.liftCoborder` is a closed immersion. The image of `f'` lies in its image,
because the open immersion is injective, and hence in the support of its kernel ideal.
That kernel is contained in the vanishing ideal of its support. The vanishing ideal of a
closed set is contained in the kernel of every morphism from a reduced scheme with image in
that set: this is the published
`Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal_and_le_ker`. So
`ker i.liftCoborder ≤ ker f'`, and `f'` factors through the closed immersion
(`IsClosedImmersion.lift`). Composing gives the factorization through `i`.

## Restricting the action

`restrictAction a i β hβ` builds the action of `G` on `Z` from a morphism
`β : G × Z ⟶ Z` with `β ≫ i = (G.X ◁ i) ≫ a.hom`, where `i` is a monomorphism. The unit
and associativity axioms (`ModObj.one_smul`, `ModObj.mul_smul`) are checked after composing
with `i` and cancelling it. They follow from the axioms of `a` (`one_smul_hom`,
`mul_smul_hom`) and naturality of the whiskering, unitor and associator.

## Main theorem

The morphism `i` is a monomorphism in `Over (Spec k)` because `i.left` is an immersion,
hence a monomorphism of schemes. `G` is locally of finite type over `k` because it is
smooth.

1. *Existence.* Let `q` be a point of `G × Z`. Its image under `G.X ◁ i` projects to
   `i (snd q)`, a point of orbit dimension `d`. By `hasOrbitDimension_act_iff`, its image
   under `a.hom` also has orbit dimension `d`, so it lies in the image of `i`. `G × Z` is
   reduced. `G` is geometrically reduced over `k` by the published
   `SmoothReducedProof.geometricallyReduced_of_smooth`, and `G` is flat over `k`. `Z` is
   reduced. It is locally of finite type over `k`, as the composite of the immersion `i`
   with `V ⟶ Spec k`, and hence locally noetherian. Mathlib's
   instance in `AlgebraicGeometry.Geometrically.Reduced` then gives that the pullback
   `G ×_k Z` is reduced. `exists_lift_of_isImmersion` factors
   `((G.X ◁ i) ≫ a.hom).left` through `i.left`. The factorization is a morphism over
   `Spec k` because `i` is. `restrictAction` turns it into the required action.
2. *Orbit dimensions.* For every action `b` with `b.hom ≫ i = (G.X ◁ i) ≫ a.hom` and every
   point `z` of `Z`, `i z` has orbit dimension `d` because it lies in the image of `i`.
   `hasOrbitDimension_iff_of_equivariant` transfers this to `HasOrbitDimension b z d`.

The theorem depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Sources and scope

The statement, its source (Conrad, *Weil and Grothendieck approaches to adelic points*,
Example 5.5) and its derivation are documented in `OrbitStratumActionRestrictionStatement.md`.
The fact that a geometrically reduced scheme times a reduced scheme is reduced (The Stacks
Project, Lemma 33.6.7, cited there) enters through Mathlib's instance for flat,
geometrically reduced morphisms and locally noetherian reduced bases. The stabilizer
squares, the immersion factorization and the restricted action are internal steps of this
proof. They are not published as separate results.
