# Descent of flatness and of fibral pure dimension for algebraic spaces

Author: Worker 3519.

## Source

Brian Conrad, *Weil and Grothendieck approaches to adelic points* (December 31,
2011), registered as `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

Printed p.13, start of Section 5: Theorem 3.4 "is valid with finitely presented
algebraic spaces in place of finitely presented schemes", by étale descent and
[Ols, Prop. 2.2], "apart from the property of having fibers non-empty and
geometrically connected of pure dimension d". Conrad continues: "By using étale
scheme covers, the condition that fibers are non-empty of pure dimension d can
be reduced to the settled scheme case", and he treats geometric connectedness
through Lemma 5.1.

Theorem 3.4(2), printed p.5, lists the properties that descend along a
directed system of rings: "closed immersion, separated, proper, smooth, affine,
flat, open immersion, finite, fibers non-empty and geometrically connected of
pure dimension `d`". The Library statement `SpaceLimitPropertyDescentStatement`
covers every entry of this list except flatness, with the last entry reduced
to "fibres nonempty and geometrically connected". This file covers the
two remaining parts: flatness, and the full last entry including pure dimension
`d`.

## Definitions

Both definitions are for a morphism `f : X ⟶ Y` of algebraic spaces over a
scheme `S`. They follow the pattern of the Library's `IsSmoothMorphism`: there
are schemes `U` and `V` over `S`, a scheme morphism `φ : U ⟶ V` over `S`, a
transformation `a : h_U ⟶ X` that is étale and surjective, and a
transformation `b : h_V ⟶ Y` that is étale, with `a ≫ hom f = h(φ) ≫ b`.

- `IsFlatMorphism f`: there is such a square with `φ` flat (`Flat φ.left`).
  Flatness of scheme morphisms is local on the source and target in the étale
  topology, and the Stacks Project ("Morphisms of Algebraic Spaces") defines
  flatness of a morphism of algebraic spaces through such étale charts. No
  representability of `f` is assumed.
- `HasPureFibreDimension d f`: there is such a square with `φ` locally of finite
  type (`LocallyOfFiniteType φ.left`) and with every residue-field fibre
  `φ.left.fiber v`, for `v` a point of `V`, pure of dimension `d` in the sense
  of the Library's `SchemeFiberGeometry.HasPureDimension`: every irreducible
  component has topological Krull dimension `d`. An empty fibre satisfies this
  vacuously.

Why the chart condition captures pure fibre dimension: for `u ∈ U` over
`x ∈ |X|`, with `v = φ(u)` over `y = f(x)`, the fibre `U_v` is étale over
`X_y ⊗ κ(v)`, and `κ(v)` is a finite separable extension of `κ(y)` because
`V → Y` is étale. Étale maps and field extensions preserve the local dimension
of a scheme locally of finite type over a field, so the local dimension of
`U_v` at `u` equals the local dimension of `X_y` at `x`. Since `a` is
surjective, every point of `X` arises this way. So all fibres of `φ` are pure
of dimension `d` exactly when all fibres of `f` are. This explanation is
provenance for the definition; the file proves nothing.

## `SpaceLimitFlatnessDimensionDescentStatement`

It is the conjunction of

1. `SpaceLimitPropertyDescends (fun f => IsFlatMorphism f)`;
2. for every natural number `d`,
   `SpaceLimitPropertyDescends (fun f => HasGeometricallyConnectedFibres f ∧ HasPureFibreDimension d f)`.

`SpaceLimitPropertyDescends P`, defined in `SpaceLimitPropertyDescentStatement`,
quantifies over a cofiltered diagram `D` of affine schemes with a limit cone
`c`, a stage `i`, and a morphism `f : X ⟶ Y` of finitely presented algebraic
spaces over `D.obj i` (each quasi-separated with a quasi-compact, locally
finitely presented étale scheme atlas). It asserts that the base change of `f`
to the limit along `c.π.app i` has `P` if and only if the base change of `f`
along `D.map g` has `P` for some `g : j ⟶ i`.

In item 2, `HasGeometricallyConnectedFibres f` is the Library's predicate: for
every field `K`, every `Spec K ⟶ S` and every `K`-point of `Y`, the points of
the fibre form a connected, hence nonempty, space. Together with
`HasPureFibreDimension d f` this is Conrad's "fibers non-empty and
geometrically connected of pure dimension `d`".

No proof is supplied here.

## Provenance

The properties and the equivalence are Conrad's. The two chart definitions are
this formalization's, modelled on the Library's `IsSmoothMorphism` and on the
étale-local definitions of the Stacks Project, as explained above. The
cofiltered diagram of affine schemes and the encoding of finite presentation
are those of `SpaceLimitPropertyDescentStatement`.
