# Intrinsic module Hom on Cartesian squares and isomorphic modules

This internal categorical construction extends intrinsic module Hom base change
from a chosen pullback object to any supplied Cartesian square. It also
transports the presheaf along ordinary module isomorphisms. Its provenance is
pullback pasting, the intrinsic module pseudofunctor, and naturality of the
pseudofunctor's composition isomorphisms; it uses no geometric existence theorem.

For a square with `p : Y ⟶ B`, `p₀ : Y₀ ⟶ B₀`, `q : Y ⟶ Y₀` and
`g : B ⟶ B₀`, a witness `h : IsPullback q p p₀ g` yields
`slicePullbackCartesianIso h`. This compares functors from `Over B` to
`Over Y₀`: first pulling back along `p` and then composing with `q`, or first
composing with `g` and then pulling back along `p₀`. At each test, paste the
test's defining pullback square with `h`, and use the resulting canonical
pullback isomorphism. Naturality follows by checking both projections. This
construction works in any category with pullbacks.

`presheafHomCongrIso F eM eN` is the analogous general construction for a
Cat-valued pseudofunctor on an opposite category. Each component pulls back
the two given object isomorphisms and conjugates an arbitrary morphism by
them. Naturality follows from the naturality of `F.mapComp'` for the inverse
source isomorphism and the target isomorphism.

For schemes, `intrinsicModuleHomCartesianIso h M₀ N₀` has type

```text
(Over.map g).op ⋙ intrinsicModuleHomPresheaf p₀ M₀ N₀
  ≅ intrinsicModuleHomPresheaf p
      ((Scheme.Modules.pullback q).obj M₀)
      ((Scheme.Modules.pullback q).obj N₀).
```

It combines the slice comparison with the pseudofunctor Hom restriction
comparison. `intrinsicModuleHomCongrIso p eM eN` specializes object-isomorphism
transport to ordinary modules on `Y`. Finally,
`intrinsicModuleHomCartesianOfIso h eM eN` composes these two comparisons when
the pullbacks of the model modules are isomorphic to supplied modules `M N`.
The resulting target is exactly `intrinsicModuleHomPresheaf p M N`.

All comparisons are natural on the entire scheme slice and retain the
explicit `ULift` to the presheaf value universe. They impose no flatness,
properness, finiteness, affine, or noetherian hypotheses. In particular, they
provide the categorical comparison needed by an actual noetherian model
without asserting existence of such a model or finite linear equations.
