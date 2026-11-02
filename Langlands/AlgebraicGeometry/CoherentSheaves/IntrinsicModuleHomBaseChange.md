# Arbitrary base change of intrinsic module Hom presheaves

This internal categorical construction follows from the intrinsic module Hom
presheaf, canonical pullback squares, and Mathlib's restriction comparison for
pseudofunctor Hom presheaves. It asserts no geometric representability theorem.

For a morphism `p : Y ⟶ B` and an arbitrary morphism `g : B' ⟶ B`,
`slicePullbackBaseChangeIso p g` compares two functors from `Over B'` to
`Over Y`. One first pulls a test back to `B' ×[B] Y` and then composes its
structure map to `Y`; the other composes the test map with `g` and then pulls
back along `p`. The component is the canonical isomorphism obtained by pasting
the two pullback squares. Naturality is checked using both projections of the
resulting pullback. This construction applies in any category with pullbacks.

For schemes and arbitrary modules `M N` on `Y`,
`intrinsicModuleHomBaseChangeIso p g M N` gives a natural isomorphism

```text
(Over.map g).op ⋙ intrinsicModuleHomPresheaf p M N
  ≅ intrinsicModuleHomPresheaf (pullback.fst g p)
      ((Scheme.Modules.pullback (pullback.snd g p)).obj M)
      ((Scheme.Modules.pullback (pullback.snd g p)).obj N).
```

The first comparison reindexes the original Hom presheaf by the canonical
pullback isomorphism. The second applies the pseudofunctor's ordinary-pullback
composition comparison to both modules. All objects and morphisms of the
slice over `B'` are included, and the explicit `ULift` to the presheaf value
universe is retained. No flatness, properness, finiteness, or affine assumption
on the morphisms or modules is used.
