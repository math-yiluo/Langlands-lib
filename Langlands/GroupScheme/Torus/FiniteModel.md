# Finite models of specified split-torus inclusions

Authors: Worker 1442.

This internal construction applies `Descent.FiniteStage.homModel` to the split
form over the original field of a specified split torus over an algebraic
extension. It retains the exact inclusion, allowing maximality to be
transported without a forward maximal-torus base-change theorem.

For fields `k` and `Ω` in any common universe `u`, an actual group `G` over
`k`, a commutative group `T` over `Ω`, and an inclusion
`i : T.toGrp ⟶ G_Ω`, `TorusFiniteModel.Model k Ω i` consists of a finite
intermediate field `E`, an actual commutative group `S` over `E`, an actual
closed inclusion `j : S.toGrp ⟶ G_E`, a proof that `S` is split, an isomorphism
`r : S_Ω ≅ T`, and the equation

```
baseChange.map j = r.hom ≫ i ≫ comparison(G).hom.
```

Here `comparison(G)` is the actual direct-to-iterated pullback comparison in
`Descent.FiniteStage`. All morphisms are actual group-scheme homomorphisms.

When `Ω/k` is algebraic, `G` has affine total scheme and is locally of finite
presentation, and the given `T` is split with `i` closed, `nonempty_model`
constructs such data and `model` chooses it. A splitting identifies `T` with
the extension of the split torus of the same finite rank over `k`.
`FiniteStage.homModel` models the resulting map to `G_Ω`; its closed-subgroup
reflection proves the model is closed. The model's source is the actual
pullback of that split torus, and the two comparison isomorphisms give the
recovery equation above.

For any such model, `Model.isMaximalTorus_baseChange` transports maximality
of the specified `i` along the source recovery and ambient comparison.
`Model.isMaximalTorus` then reflects maximality to `E` using the independent
field-extension reflection theorem. Neither result invokes forward
preservation of arbitrary maximal tori, or a no-torus unipotence result.

The provenance is the published split-torus presentation and base-change
isomorphism, finite-stage homomorphism construction, closed-subgroup
reflection, and maximality transport/reflection. Frobenius invariance and
effective descent to `k` remain separate obligations; this module does not
construct an invariant geometric maximal torus.
