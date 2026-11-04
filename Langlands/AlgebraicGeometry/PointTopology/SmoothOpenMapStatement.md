# Smooth morphisms are open on local-field rational points

Author: Worker 1505.

`Langlands.AlgebraicGeometry.PointTopology.SmoothRationalPointOpenMapStatement.{u}`
is a Prop-valued proposition. It quantifies over:

- a field `F : Type u` with `ValuativeRel F`, a topology, and
  `IsNonarchimedeanLocalField F`;
- objects `X` and `Y` of `Over (Spec (CommRingCat.of F))` whose underlying
  schemes are affine (`IsAffine X.left`, `IsAffine Y.left`);
- a morphism `f : X ⟶ Y` over `Spec F` whose underlying scheme morphism is
  smooth (`Smooth f.left`, Mathlib's `AlgebraicGeometry.Smooth`).

For these data it asserts that

```text
fun p : RationalPoint F X => p ≫ f
```

is an open map. Here `RationalPoint F X` is the published actual carrier
`Over.mk (𝟙 (Spec F)) ⟶ X`, and both point sets carry the published
`rationalPointTopology`: the global-section evaluation topology transported to
this carrier. The map is ordinary composition of actual relative morphisms. For
a group scheme `G`, `GroupScheme.rationalPoints G` is this same carrier for
`G.X`, and `GroupScheme.rationalPoints.map q` is postcomposition with
`q.hom.hom`. A smooth group-scheme homomorphism with affine source and target
is therefore a direct instance.

## Source and scope

Brian Conrad, *Weil and Grothendieck approaches to adelic points* (notes dated
December 31, 2011), registered source
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`:

- printed page 11, in the paragraph after Proposition 4.4 that introduces
  Theorem 4.5. If `X' → X` is a smooth `K`-morphism of algebraic `K`-schemes,
  where `K` is complete for a nontrivial absolute value, then
  `X'(K) → X(K)` is open. The same paragraph sketches the proof: an étale
  map to affine space, the local structure of étale maps, and continuity of
  simple roots.
- printed page 12, step (i) of the proof of Theorem 4.5. The same fact is
  restated for smooth maps between `K`-schemes locally of finite type.

The statement specializes this to `K = F`, a nonarchimedean local field.
Mathlib's `IsNonarchimedeanLocalField` makes `F` a complete, nontrivially
valued field, and its given topology is the valuation topology. Conrad's
schemes are arbitrary algebraic (locally finite type) schemes; this statement
covers the affine case, which is what the point-topology interface uses.

The statement also drops one hypothesis: it does not require `Y` to be of
finite type over `F`. Smoothness of `f` makes `X` locally of finite
presentation over `Y`, and the evaluation topology on `Y(F)` uses all global
sections of `Y`. Openness is local. Near a point it involves only the finitely
many coefficients of one local standard-smooth presentation of `f`, so this
generalization holds by the same implicit-function argument. If `Y` is of
finite type over `F`, the statement is exactly the affine case of Conrad's.

This is a statement unit only; the proof is a separate obligation.
