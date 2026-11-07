# Geometric components under an extension of the base field

This is an internal construction from the published chosen geometric-component
comparison, actual pullback-tower isomorphism and component-map laws. It introduces
no external structural assertion.

Let `k` and `K` be arbitrary fields in the same arbitrary universe, with a
specified `k`-algebra structure on `K`. Let `H` be an actual smooth affine group
scheme over `Spec k`. The `k`-algebra structure on `AlgebraicClosure K` is the
canonical one induced through `K`. We supply an
`AlgebraicClosure k`-algebra structure on `AlgebraicClosure K`, compatible with
this structure and the canonical embedding of `k` into its chosen closure.
Thus the two maps from `k` to `AlgebraicClosure K` agree. The closure embedding
is part of the data; its existence or independence is not asserted here.
There is no algebraicity, separability, perfection, characteristic,
connectedness or reductivity restriction on the original extension or group.

`geometricComponentBaseChangeEquiv k K H` is a multiplicative equivalence
between the full actual connected-component groups

```
GeometricComponents k H
  ≃* GeometricComponents K (baseChanged k K H).
```

The source is the connected-component space of `H` pulled back to
`AlgebraicClosure k`. The target is the connected-component space of the
iterated pullback, first to `K` and then to `AlgebraicClosure K`.
The construction first applies `geometricComponentEmbeddingEquiv` along the
specified closure embedding to reach the direct pullback of `H` to
`AlgebraicClosure K`. It then applies the inverse of `allComponentIso` of
`towerBaseChangeIso`, which identifies the iterated and direct pullbacks.
These are the published actual component groups and maps.

`geometricComponentBaseChangeHomeomorph` has the same underlying equivalence.
Its topologies are the inherited connected-component quotient topologies of
those actual schemes. They are finite and discrete for these smooth affine
groups. Continuity in both directions therefore follows from the published
discreteness instances. Its application lemma is definitional.

`geometricComponentBaseChangeSectionHom` is an actual group homomorphism
from the sections over `AlgebraicClosure k` to the sections of the iterated
pullback over `AlgebraicClosure K`. Its construction composes
`fieldEmbeddingSectionHom k (AlgebraicClosure k) (AlgebraicClosure K) H`
with the rational-point map of the inverse of
`towerBaseChangeIso k K (AlgebraicClosure K) H`.
The section formula `geometricComponentBaseChangeEquiv_ofPoint` proves

```
geometricComponentBaseChangeEquiv k K H
    (geometricComponentOfPoint k H x)
  = geometricComponentOfPoint K (baseChanged k K H)
      (geometricComponentBaseChangeSectionHom k K H x).
```

Thus it computes the comparison on every actual section, with the exported
section homomorphism naming the actual composite just described.

The action comparison retains compatible automorphisms as explicit data.
For `σ` in the absolute Galois group of `k` and `τ` in that of `K`, assume

```
τ(iota(a)) = iota(σ(a))
```

for every `a : AlgebraicClosure k`, where `iota` is the specified closure
embedding. Then `geometricComponentBaseChangeEquiv_smul` proves

```
geometricComponentBaseChangeEquiv k K H (σ • c)
  = τ • geometricComponentBaseChangeEquiv k K H c.
```

Both actions are the actual continuous absolute Galois actions already
constructed on chosen geometric components.

Two intrinsic tower lemmas implement the action calculation.
`GaloisPointComparison.towerBaseChangeIso_conjugate` works for arbitrary
compatible field towers `k → K → M`, without smoothness or affineness. On actual
sections, the direct/iterated pullback comparison intertwines coefficient
conjugation by an automorphism of `M` over `K` with conjugation by its scalar
restriction over `k`. The proof applies the injective original-coefficient
comparison and uses the published tower and coefficient-conjugation formulas.
For algebraically closed `M` and smooth affine `H`,
`allComponentIso_tower_conjugate` lifts this equality to all actual components:
each component has an actual section, and the section formula reduces the
claim to the preceding equality.

The implementation packages the actual inverse section map, component
equivalence, section law and action law in a private `TowerComponentData`.
Its verified constructor `towerComponentData` uses the actual tower
isomorphism while all three fields are abstract. A private helper proves the
inverse component-isomorphism section formula for an arbitrary actual
isomorphism by `allComponentMap_ofPoint`. The tower package is opaque to
subsequent elaboration; its body and laws are fully proved.

The second verified package, `fieldBaseChangeComponentData`, specializes the
tower package at `M = AlgebraicClosure K` and constructs the two composites.
Its section formula applies the inverse component equivalence to the published
`geometricComponentEmbeddingEquiv_ofPoint` equality, then uses the stored
inverse section formula. For the action formula, apply the injective forward
tower equivalence, cancel its inverse, and combine the stored tower action law
with `geometricComponentEmbeddingEquiv_smul`. The exported equivalence,
section homomorphism and two laws are projections of this package. Naming the
actual maps this way avoids repeatedly unfolding the large pullback-tower
construction when specializing to chosen closures.

This unit constructs neither an embedding-independent comparison nor an
absolute Galois restriction homomorphism. It does not assert effective descent,
surjectivity on rational points, or an identification with the points of an
fppf quotient.
