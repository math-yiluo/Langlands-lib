# Quotient classification of actual square-zero Picard lifting fibres

This is an internal construction from the published
`SquareZeroPicardObstruction` exactness results and Mathlib's first isomorphism
theorem for additive groups. It introduces no external source assertion.
Let `i : Y ⟶ X` be an actual closed immersion of schemes in any universe `u`,
with compact underlying spaces and `i.ker ^ 2 = ⊥`. No splitting is assumed.
Write `I = StructureKernelModule.kernelModule i`, and let
`b : H⁰(Y,O_Yˣ) → H¹(X,I)` be `SquareZeroUnitCohomology.boundaryMap i hi 0`.
Both cohomology groups and this boundary are the published actual sheaf
cohomology constructions. In particular, ideal cohomology is the underlying
additive group of the actual derived module cohomology of `I`.

The additive group `infinitesimalClasses i hi` is the quotient
`H¹(X,I) / image(b)`. Its subgroup of relations is the additive image of the
actual unit boundary. No scalar stability of that image is asserted.
The map `oneAddToKernel` is the published actual `oneAddPicardMap` with
codomain restricted to the kernel of `Group.pullback i`, the pullback on the
existing scheme Picard groups. The published image criterion shows that
this restriction is surjective. The published kernel criterion identifies
its kernel with `image(b)`. Mathlib's first isomorphism theorem then gives
`infinitesimalClassesEquivKernel`, an additive equivalence from the quotient
to the actual Picard pullback kernel. Its value on the quotient class of
`a : H¹(X,I)` is exactly the actual `1+a` Picard class, recorded by
`infinitesimalClassesEquivKernel_mk` and `coe_oneAddToKernel`.

For `y : Group Y` and a chosen lift `x : Group X` satisfying
`Group.pullback i x = y`, `kernelEquivFibre` translates a kernel element
`k` to `k + x`; its inverse subtracts `x` from a fibre element. These two
formulas are inverse by the additive group laws. Composing this translation
with the quotient/kernel equivalence gives

```text
infinitesimalClassesEquivFibre :
  H¹(X,I) / image(b) ≃ {x' : Pic(X) // pullback(i,x') = y}.
```

`coe_infinitesimalClassesEquivFibre_mk` states the representative formula:
the class of `a` maps to `oneAddPicardMap i hi a + x`. Thus each nonempty
ordinary Picard lifting fibre is explicitly classified by the quotient,
after choosing a lift. The fibre is only used as a type; no canonical group
law on it is claimed. The underlying Picard groups are those of actual
tensor-invertible module sheaves, and their pullback is actual scheme-module
pullback.

This module does not assert a scalar-vector-space structure on the quotient,
base-change compatibility, finiteness, or representability of a family of
lifting fibres or of the actual fppf Picard sheaf.
