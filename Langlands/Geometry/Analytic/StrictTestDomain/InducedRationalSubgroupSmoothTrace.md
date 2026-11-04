# Smooth full coefficient trace for actual rational subgroup restriction

This internal construction specializes the existing full smooth coefficient
pullback and sheaf trace to the original rational subgroup-restriction map.
It constructs the source local stable-neighbourhood property by restricting
the original target action. Covering and finite original fibers are supplied
by the proved subgroup geometry, and the trace counts every relative coset.

The inputs are a complete ultrametric normed field `K : Type u`, a presented
strict affinoid algebra `P` over `K`, a topological group `G : Type u`, an
original `RationalSpectralAction G P`, open subgroups `V ≤ U`, and an original
`U`-invariant rational domain `d`. Write

```text
X = (inclusion V).obj ((ρ.invariantRestrictionFunctor h).obj d),
Y = (inclusion U).obj d,
f = subgroupRestriction h d : X ⟶ Y,
D = U / (V.toSubgroup.subgroupOf U.toSubgroup).
```

The field, algebra, group, coefficient ring, induced spaces and coefficient
carriers share arbitrary universe `u`, as required by the existing smooth
direct-image API. The ring `R : Type u` is any commutative ring. Coefficients
range over the entire original `SmoothRep.{u,u,u} R G` category, with all
original intertwiners and no coefficient topology, dimension or admissibility
restriction.

The one local geometric premise is

```text
HasStableNeighbourhoods Y.subgroup.toSubgroup Y.LocalSpectrum.
```

Its action is the original `localSpectrumSubgroupMulAction Y`. There is no
additional local stable-neighbourhood premise for `X`. The full-object
subgroup expression in Lean fixes the original action when elaborating this
premise.

`subgroupRestriction_hasStableNeighbourhoods` constructs that property for
the original action on `X.LocalSpectrum`. The source and target have the same
original local Banach spectrum and topology, and the source action is
definitionally the target action restricted along the actual inclusion
`i : V.toSubgroup →* U.toSubgroup`. For a point and open neighbourhood, take
the target property's open subgroup `H` and stable open `W`. The inclusion is
continuous for the original subtype topologies. `H.comap i` is therefore an
open subgroup of `V`, and the very same `W` is stable under it: its action is
the original target action by `i v`. This proves every field of the source
property. The local instance `sourceStable` supplies it to the subsequent
constructions. Ambient stable neighbourhoods on both original induced
spectra are constructed by the imported `SmoothSheafVariation` interface.

Let `L_X` and `L_Y` denote its existing full smooth coefficient sheaf
functors, and let `S_f = SmoothSheafVariation.directImage R f`. This is the
actual smooth coreflection of the ordinary inverse-open direct image.
For every original coefficient `M`,
`subgroupRestrictionSmoothCoefficientMap` is the morphism

```text
L_Y(M) ⟶ S_f(L_X(M)).
```

It specializes the existing smooth coefficient pullback at the unchanged
original arrow `f`. The target coefficient sheaf retains every locally
constant section on each original open; the stable-neighbourhood premise
proves its smoothness. No sections are removed from the coefficient sheaf.
The smooth direct image itself has its existing subsheaf inclusion into the
ordinary direct image.

`subgroupRestrictionSmoothCoefficientNatTrans` packages pullback over the
entire original smooth coefficient category, and its component lemma
identifies each component definitionally with this map.
`subgroupRestrictionSmoothCoefficientMap_inclusion` proves that forgetting
smoothness and composing with the actual direct-image inclusion gives
exactly `SheafVariation.coefficientMap f M.representation`. Thus the original
inverse-open pullback, original coefficient module and action are retained.

The trace section additionally assumes `Finite D`. The local instance
`finite_subgroupRestrictionSmoothFiber` uses the imported theorem to prove
finiteness of every entire literal fiber of `f.inducedMap`. The covering
predicate is also the imported proved predicate of that same map.
Neither predicate is an additional input. In particular, the map remains
the original full `G`-equivariant map `[g,x]_V ↦ [g,x]_U`.

`subgroupRestrictionSmoothCoefficientTrace` is the morphism

```text
S_f(L_X(M)) ⟶ L_Y(M).
```

It is precisely the existing smooth rational coefficient trace with those
proved geometric inputs.
`subgroupRestrictionSmoothCoefficientTrace_forget` states that its image
under `smoothInclusion` is the actual smooth-direct-image inclusion followed
by `subgroupRestrictionCoefficientTrace h d M.representation`. The latter
is the full ordinary subgroup trace, so this equality identifies the
underlying operation without introducing a comparison hypothesis.

For an original target action open `A`, a section `s` of the smooth direct
image over `A`, and `y : A.openSet`,
`subgroupRestrictionSmoothCoefficientTrace_apply` evaluates this trace as

```text
fiberSum (DirectImage.pointMap f.inducedMap f.inducedMap_smul A) s.val y.
```

Here `s.val` is the original locally constant section on the actual
inverse-image open; its separate smoothness proof is not evaluated. The
restricted point map and all open-membership proofs are the existing ones.
The sum is unnormalized.

With a `Fintype D` instance,
`subgroupRestrictionSmoothCoefficientTrace_apply_sum` presents exactly
that value as

```text
∑ c : D, s.val ⟨(subgroupRestrictionFiberHomeomorph h d y.val c).val, _⟩.
```

The displayed subtype proof places this point in the actual inverse-image
open using its fiber equality and `y.property`. The reindexing equivalence
first identifies `D` with the entire original literal fiber by the proved
homeomorphism, then uses the inverse of `DirectImage.pointMapFiberEquiv` to
identify that fiber with the restricted point-map fiber. Applying
`fiberSum_eq_sum` to this composite proves the formula. There is no chosen
subfiber or extension of the inverse-open section. `Finite D` suffices for
construction; `Fintype D` only displays the sum. No equivariance of the
chosen fiber homeomorphism is asserted.

`subgroupRestrictionSmoothCoefficientTrace_pullback_apply` proves for
every original target open, locally constant section `s` and point `y` that
smooth pullback followed by trace evaluates to

```text
V.toSubgroup.relIndex U.toSubgroup • s y.
```

This is natural-number scalar multiplication. The proof applies the generic
smooth pullback-trace formula, which counts the whole original literal
fiber, and rewrites its cardinality by the proved original-map relative-index
theorem. It neither assumes a degree nor divides by the index.

`subgroupRestrictionSmoothCoefficientTraceNatTrans` packages the trace as
a natural transformation `L_X ⋙ S_f ⟶ L_Y`. Its component lemma is
definitional. `subgroupRestrictionSmoothCoefficientTrace_naturality`
states its square for every original smooth coefficient intertwiner:
direct image of the source coefficient map followed by trace equals trace
followed by the target coefficient map. This follows from the existing
trace natural transformation, so all coefficient maps are retained.

The provenance is internal. The new local stability proof uses the original
subgroup inclusion, open-subgroup inverse image and the unchanged restricted
action. The remaining constructions specialize
`InducedRationalSmoothSheafTrace` and `InducedRationalSubgroupTrace` using
the original-map geometry from `InducedRationalSubgroupCovering`. Intrinsic
sheaf, linearity, equivariance and naturality obligations are proved by
those existing constructions; the full-coset sum and numerical degree are
proved by the explicit reindexing and cardinality substitution above. No
external Harris or Berkovich theorem is claimed.

This unit treats subgroup change with the rational presentation fixed and
ordinary-open degree-zero smooth coefficient sheaves. It retains the
original target local stable-neighbourhood premise. General rational-domain
coverings, analytic and etale realization, Godement and higher derived
traces, geometric compact-support comparison, arithmetic Hecke
identification, Shimura specialization and Harris compatibility remain
obligations of the broader task.
