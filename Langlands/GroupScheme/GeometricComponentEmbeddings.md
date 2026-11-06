# Comparing chosen geometric components along a specified closure embedding

This is an internal specialization of the published `GeometricComponents` and
`ComponentFieldEmbeddings` constructions. It uses their actual pullbacks,
full component groups, section formulas and coefficient actions. It introduces
no new external structural assertion.

Let `k` and `L` be fields in an arbitrary common universe `u`. Supply algebra
structures `k → L` and `AlgebraicClosure k → L`, with
`IsScalarTower k (AlgebraicClosure k) L`. The latter algebra structure specifies
an embedding of Mathlib's chosen algebraic closure into `L`; the scalar-tower
law makes it compatible with the given embedding of `k`. Assume that `L` is
algebraically closed. No algebraicity of `L / k` is required.

For an actual smooth affine group scheme `H` over `Spec k`,
`geometricComponentEmbeddingEquiv k L H` is a multiplicative equivalence

```text
GeometricComponents k H ≃* AlgebraicallyClosedComponents H_L.
```

The source is the full actual component group after pullback to the chosen
`AlgebraicClosure k`, with its published continuous absolute Galois action.
The target is the full actual component group of the direct pullback to `L`.
The construction is `componentFieldEmbeddingEquiv` specialized to the
specified embedding `AlgebraicClosure k → L`. That published construction
extends actual sections and composes the component base-change equivalence
with the actual iterated-to-direct pullback isomorphism.

`geometricComponentEmbeddingHomeomorph` equips the same underlying equivalence
with continuity in both directions. Both topologies are the existing
connected-component quotient topologies; both are discrete by the published
finite-component results for smooth affine groups over algebraically closed
fields. The proof therefore uses `continuous_of_discreteTopology` in each
direction. Its evaluation formula identifies the homeomorphism with the
multiplicative equivalence.

`geometricComponentEmbeddingEquiv_ofPoint` identifies the comparison on every
actual section over the chosen algebraic closure. It sends that section's
component to the component of `fieldEmbeddingSectionHom`, which extends the
section along the specified embedding and applies the actual pullback tower
isomorphism. This is the published component section formula under the chosen
specialization.

`geometricComponentEmbeddingEquiv_smul` takes
`σ : Field.absoluteGaloisGroup k`, a `k`-algebra automorphism `τ` of `L`, and
the explicit condition

```text
τ (algebraMap (AlgebraicClosure k) L a) =
  algebraMap (AlgebraicClosure k) L (σ a)   for every a.
```

It proves that the equivalence sends `σ • c` to the coefficient conjugate by
`τ` of the image of `c`. The proof unfolds the chosen action to the existing
component action and specializes the published equivariance law with precisely
this compatibility condition. It does not assert that arbitrary automorphism
pairs satisfy that condition or supply an extension of each automorphism.

For every actual homomorphism `f : H → H'` over `k`, with both groups smooth
and affine, `geometricComponentEmbeddingEquiv_naturality` proves that the
equivalences commute with `geometricComponentMap k f` and the component map
of the actual pullback of `f` to `L`. Its proof is the published naturality
law under the same specialization.

There is no algebraic-closedness assumption on `k`, and no characteristic,
perfection, connectedness or reductivity restriction. The comparison depends
on the supplied embedding of the chosen closure. It asserts no independence
from that embedding, realization as an étale group scheme, or effective
descent or rational-point surjectivity for Galois-invariant components.
