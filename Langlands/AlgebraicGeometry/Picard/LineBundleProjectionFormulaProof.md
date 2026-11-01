# Proof of the line-bundle projection formula

`lineBundleProjectionFormula` proves
`LineBundleProjectionFormulaStatement` for every scheme morphism, line
bundle, and module sheaf in the stated universe.

The private `tensorInverseEquivalence` starts with an isomorphism
`e : L ⊗ N ≅ 𝟙_ C` in a braided monoidal category. Left tensoring by `N`
and by `L` are inverse functors. The unitors, tensoring of `e` and its
braided version, and `tensorLeftTensor` construct the required two natural
isomorphisms. `Equivalence.mk` adjusts the unit to satisfy the adjunction
triangle, retaining the specified functor and inverse.

For a strong monoidal `F : C ⥤ D` with right adjoint `G`, the private
`tensorInverseProjectionIso` transports `e` through the tensorator and unit
isomorphism of `F`. It obtains tensor-inverse equivalences in `C` and `D`.
Their adjunctions compose with `F ⊣ G` to give

```
tensorLeft N ⋙ F       ⊣ G ⋙ tensorLeft L
F ⋙ tensorLeft (F N)   ⊣ tensorLeft (F L) ⋙ G.
```

`Functor.Monoidal.commTensorLeft` identifies the two left adjoints.
`Adjunction.rightAdjointUniq` therefore identifies the two right adjoints.
This constructs the required projection isomorphism without asserting a
formula for the canonical projection morphism.

For actual sheaves, `locallyFreeRankOneTensorInvertible` supplies a tensor
inverse of `L.obj`. The actual pullback is strong monoidal by the published
`PullbackMonoidal`; its actual right adjoint is scheme-module pushforward.
Taking the component at `M` gives the isomorphism for the localized
monoidal tensor. `localizedTensorIso`, and its image under pushforward,
convert the two ends to the explicit sheafified `tensorObj`. This is
`lineBundleProjectionIso f L M`, whose existence proves the target.

This proof is an internal consequence of the published actual
constructions and Mathlib's adjunction uniqueness. No affineness,
flatness, quasi-coherence, or cohomological comparison assumption is used.
