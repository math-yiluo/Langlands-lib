# The actual automorphism presheaf of a line bundle

This is a derived construction from `LineBundle.unitAutEquiv`, the actual
line-bundle pseudofunctor `PicardGroupoid.pseudofunctor`, Mathlib's
`Pseudofunctor.presheafHom`, and the ordinary presheaf of global units
`Gm.unitsFunctor`. It introduces no new assertion translated from external
literature.

Let `X` be any scheme in universe `u` and `L` an actual line bundle on `X`.
`unitHomEquiv L` sends a unit of the ordinary ring of global functions to the
corresponding scalar automorphism, regarded as a morphism in the core of the
category of actual line bundles. It is a bijection because
`LineBundle.unitAutEquiv` is a multiplicative equivalence.

For `T → X`, `automorphismEquivAt L T` applies this bijection to the actual
pullback of `L` to `T`. Its codomain is exactly the value of Mathlib's
`pseudofunctor.presheafHom (Core.mk L) (Core.mk L)`. The restriction maps of
this presheaf include the composition isomorphisms of the pseudofunctor.
`pullHom_unitHomEquiv` proves compatibility with those full restriction
maps: scalar pullback gives the unit pulled back along the test-scheme
morphism, and conjugation by the composition isomorphism preserves that
scalar. `automorphismEquivAt_naturality` specializes this formula to
morphisms in the entire slice category `Over X`.

`unitsAutomorphismPresheafIso L` assembles these bijections into a natural
isomorphism from `Gm.unitsFunctor X ⋙ forget CommGrpCat` to that actual
automorphism presheaf. A private general construction assembles pointwise
equivalences of type-valued functors from their elementwise naturality;
using it avoids repeatedly expanding the concrete pseudofunctor's
composition data during kernel checking.

For any morphism `f : X → S`, `relativeAutomorphismPresheaf f L` restricts
the same automorphism presheaf along `Over.pullback f` and lifts its values
to universe `u + 1`, as required by the algebraic-space presheaf convention.
`relativeUnitsAutomorphismPresheafIso f L` identifies it with
`RelativeGlobalUnits.presheaf f`. The latter's value at every `T → S` is
the units of the global functions on the actual fibre product `T ×ₛ X`.
The identification follows by whiskering the preceding natural isomorphism;
the intermediate units functor agrees with `RelativeGlobalUnits.presheaf f`
on objects and restriction maps.

All test schemes and all test-scheme morphisms are included. There are no
properness, flatness, finiteness, field or nonemptiness hypotheses. This
construction concerns actual automorphisms rather than isomorphism classes;
it does not assert geometric representability or smoothness of their
presheaf.
