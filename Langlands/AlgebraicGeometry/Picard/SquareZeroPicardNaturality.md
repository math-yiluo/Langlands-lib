# Actual Picard deformation classes for nested square-zero thickenings

Fix actual scheme morphisms `i : Y ⟶ X` and `j : Z ⟶ Y` in an arbitrary
common universe `u`. The scheme Picard groups `Group X`, `Group Y`, and
`Group Z` are the existing additive groups of isomorphism classes of
actual tensor-invertible module sheaves. `Group.pullback` is induced by
actual scheme-module pullback.

For any such two morphisms, `pullbackKernelMap i j` maps
`ker(pullback i)` into `ker(pullback (j ≫ i))` by retaining the
ambient Picard class. The map is well defined by the published identity

```text
Group.pullback (j ≫ i) = (Group.pullback j).comp (Group.pullback i).
```

It is an additive homomorphism, and `coe_pullbackKernelMap` records its
underlying value. The lemma `pullbackKernelMap_injective` follows by
applying the underlying-value function to an equality of images.
These constructions impose no immersion or compactness hypothesis.

For every `y : Group Y`, `fibreMap i j y` is likewise the map

```text
{x : Group X // Group.pullback i x = y}
  → {x : Group X // Group.pullback (j ≫ i) x = Group.pullback j y}
```

which retains `x`. Pullback composition proves its fibre condition.
`coe_fibreMap` and `fibreMap_injective` record its value and injectivity.
The fibres are used only as types.

The remaining constructions assume that `i` and `j ≫ i` are closed
immersions with `hi : i.ker ^ 2 = ⊥` and
`hji : (j ≫ i).ker ^ 2 = ⊥`. No separate immersion or nilpotence
hypothesis on `j` is used. Write

```text
I = StructureKernelModule.kernelModule i
J = StructureKernelModule.kernelModule (j ≫ i)
b_i = SquareZeroUnitCohomology.boundaryMap i hi 0
b_ji = SquareZeroUnitCohomology.boundaryMap (j ≫ i) hji 0
f = SquareZeroUnitNaturality.idealCohomologyMap i j 1.
```

Here `I` and `J` are actual structure-section kernel modules on `X`,
and `f` is induced by their actual inclusion as module sheaves.
The boundaries `b_i` and `b_ji` are the published actual unit-sequence
connecting maps transported to actual ideal-module H¹. Their domains
are actual unit-sheaf H⁰ on `Y` and `Z`. All these sheaves are on
small Zariski sites.

The lemma `boundaryImage_le` proves

```text
image(b_i) ≤ f⁻¹(image(b_ji)).
```

For a representative `b_i(y)`, its proof exhibits the unit-cohomology
class `quotientUnitCohomologyMap i j hi hji 0 y` as a preimage of
`f(b_i(y))` under `b_ji`, using `boundaryMap_naturality`.
The quotient-unit cohomology map here is the explicit transported map
of `SquareZeroUnitNaturality`, through the existing nilpotent
pushforward equivalences.

The definition `infinitesimalClassesMap i j hi hji` applies Mathlib's
`QuotientAddGroup.map` to `f` with this relation-preservation proof.
It is the additive homomorphism

```text
H¹(X,I) / image(b_i) →+ H¹(X,J) / image(b_ji).
```

Both groups are exactly the existing `SquareZeroPicardFibres.infinitesimalClasses`.
`infinitesimalClassesMap_mk` states that the class of `a` maps to the
class of `f(a)`; its proof is reflexive. These quotient constructions
do not require compactness.

When `X` has compact underlying space,
`oneAddPicardMap_naturality` proves

```text
oneAddPicardMap (j ≫ i) hji (f(a)) = oneAddPicardMap i hi a.
```

The proof applies the injective actual unit-H¹/Picard classifier
`Group.unitCohomologyAddEquiv X`. The published comparison
`cohomology_oneAddPicardMap` reduces the equation to
`SquareZeroUnitNaturality.oneAddMap_naturality`.
No intrinsic quotient-unit comparison for `j` is needed.

Assume in addition that `Y` and `Z` have compact underlying spaces.
Let `E_i` and `E_ji` be the existing additive equivalences
`infinitesimalClassesEquivKernel i hi` and
`infinitesimalClassesEquivKernel (j ≫ i) hji`.
For every quotient class `q`, the lemma
`infinitesimalClassesEquivKernel_naturality` states

```text
E_ji(infinitesimalClassesMap i j hi hji q)
  = pullbackKernelMap i j (E_i(q)).
```

Quotient induction reduces this equation to a representative. The
representative formulas for the existing classifiers then reduce it
to `oneAddPicardMap_naturality`. Consequently
`infinitesimalClassesMap_injective` holds: apply `E_ji` to an equality
of images, use this compatibility, and cancel the injective kernel
map and `E_i`.

Finally, suppose `x : Group X` lifts `y : Group Y`, with
`hx : Group.pullback i x = y`. Its further pullback is
`Group.pullback j y` by composition. The theorem
`infinitesimalClassesEquivFibre_naturality` states that the existing
fibre classifier for `j ≫ i`, using the same lift `x`, sends the
image of `q` to

```text
fibreMap i j y (infinitesimalClassesEquivFibre i hi y x hx q).
```

The proof uses the quotient/kernel compatibility and the definition
of each fibre classifier as translation by `x`. Thus the actual
map on ambient Picard classes agrees with the induced map on the
explicit deformation parameters.

This is an internal derived construction from the actual unit
naturality, the existing actual square-zero Picard obstruction and
quotient/fibre classification, the published Picard pullback
composition law, and Mathlib's additive quotient construction.
No additional external mathematical assertion is assumed.
The quotients are additive groups; no scalar stability of their
boundary relations, vector-space structure, general scheme
base-change theorem, family representer, or final fppf Picard
representability is asserted.
