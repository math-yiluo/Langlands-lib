# Projection formula for an actual line bundle

`LineBundleProjectionFormulaStatement` asserts that for any scheme morphism
`f : X ⟶ Y`, line bundle `L` on `Y`, and actual module sheaf `M` on `X`,
there exists an isomorphism

```
tensorObj L.obj (f_* M) ≅ f_* (tensorObj (f* L.obj) M).
```

All sheaf functors and tensor objects are the published actual
scheme-module constructions. The statement requires neither an affine,
finite, flat, or proper morphism nor quasi-coherence of `M`.
The line bundle means an actual sheaf locally free of rank one.
The conclusion is existence of an isomorphism; it does not specify the
canonical projection morphism or a compatibility law for such a morphism.

This is a derived categorical consequence of the published
`locallyFreeRankOneTensorInvertible`, the strong monoidal pullback in
`PullbackMonoidal`, and Mathlib's actual
`Scheme.Modules.pullbackPushforwardAdjunction`.
Tensoring with a tensor-invertible object has tensoring with an inverse as
an equivalence. Strong monoidal pullback commutes with tensoring by that
inverse. Composing the corresponding tensor adjunctions with the
pullback-pushforward adjunction identifies their right adjoints.
The published `localizedTensorIso` converts the resulting monoidal tensor
objects to the explicit sheafified `tensorObj` in this statement.

This internal derivation supplies an isomorphism needed for the finite-map
Euler comparison. It makes no assertion about cohomological finiteness,
Euler polynomiality, or native rank.
