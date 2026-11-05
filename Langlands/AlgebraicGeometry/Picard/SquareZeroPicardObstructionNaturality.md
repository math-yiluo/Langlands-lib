# Intrinsic naturality of actual square-zero Picard obstructions

This internal construction combines the published actual Picard/unit-H¹
pullback comparison with the published intrinsic naturality of the
actual unit-sequence boundary. It assumes no further external mathematical
assertion.

Fix schemes `X`, `Y`, `Z` in any common universe `u`, with compact underlying
spaces for `Y` and `Z`. Let `i : Y ⟶ X` and `j : Z ⟶ Y` satisfy
`IsClosedImmersion i`, `IsClosedImmersion (j ≫ i)`, and
`IsClosedImmersion j`. Supply square-zero kernel witnesses
`hi : i.ker ^ 2 = ⊥`, `hji : (j ≫ i).ker ^ 2 = ⊥`, and an explicit
nilpotent-kernel witness `hj : IsNilpotent j.ker`. No compactness of `X`
is required until the final liftability criterion.

Write `o_i = SquareZeroPicardObstruction.obstructionMap i hi` and
`o_ji = SquareZeroPicardObstruction.obstructionMap (j ≫ i) hji`. These are
the unchanged actual obstruction maps: the published additive
Picard/unit-H¹ equivalence followed by the actual unit-sequence connecting
map into actual ideal-module H². The map
`f = SquareZeroUnitNaturality.idealCohomologyMap i j 2` is induced by the
actual inclusion of the structure-kernel module for `i` into the
structure-kernel module for `j ≫ i`, both on `X`. The scheme Picard
pullback `Group.pullback j` uses the existing actual module-sheaf pullback.

`obstructionMap_naturality` proves, for every `y : Group Y`,

```text
o_ji(Group.pullback j y) = f(o_i(y)).
```

Unfolding the obstruction maps reduces this to the published
`Group.unitCohomologyAddEquiv_pullback j hj` and
`SquareZeroUnitNaturality.boundaryMap_cohomologyMap i j hi hji hj 1`.
The latter is the intrinsic restriction theorem from
`UnitH1PullbackComposition`; the new proof uses the actual pullback on
Picard groups rather than introducing another quotient-unit map.
`obstructionMap_comp_pullback` records the same identity as equality
of additive homomorphisms.

It follows that actual Picard pullback preserves vanishing of the
actual obstruction, as stated by `obstructionMap_pullback_eq_zero`.
The definition `obstructionKernelMap` restricts `Group.pullback j` to
an additive homomorphism

```text
ker(o_i) →+ ker(o_ji).
```

The naturality identity proves the target kernel condition; the
homomorphism laws come from the existing Picard pullback homomorphism.
`coe_obstructionKernelMap` records its actual underlying Picard class.

If `f` is injective, `obstructionMap_pullback_eq_zero_iff` shows that
further pullback also reflects obstruction vanishing: rewrite by
naturality and cancel `f`, which preserves zero. This is an explicit
additional hypothesis, not an injectivity claim about ideal H² maps.
If `X` also has compact underlying space, the published
`SquareZeroPicardObstruction.picard_lift_iff` on each immersion converts
this into `picard_lift_further_pullback_iff`: the actual class `y` lifts
to `Pic(X)` exactly when its pullback to `Z` lifts to `Pic(X)`, under
that same injectivity hypothesis.

This contribution concerns nested closed immersions and their actual
obstruction groups. It proves no general scheme base-change theorem,
unconditional injectivity of ideal-cohomology maps, scalar stability,
representability of a family, or final fppf Picard representability.
