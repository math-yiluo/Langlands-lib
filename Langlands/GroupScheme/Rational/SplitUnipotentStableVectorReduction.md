# Central stable vector subgroups from perfect-field splitness

This module serves the proof of
`Langlands.GroupScheme.RelativeRoot.SplitUnipotentStableVectorSubgroupStatement`
(task 6b07dcd2-af39-4c69-8ade-d0faa997a49f). It has one theorem, in the
namespace `Langlands.GroupScheme.RelativeRoot`.

`splitUnipotentStableVectorSubgroup_of_perfectFieldUnipotentSplit`. Assume
`Langlands.GroupScheme.PerfectFieldUnipotentSplitStatement` in universe u:
over every perfect field, every smooth connected affine unipotent group scheme
is split unipotent. Then `SplitUnipotentStableVectorSubgroupStatement` holds in
universe u.

The statement takes the hypothesis as a premise. The final proof of the target
applies this theorem to a proof of the hypothesis.

## Proof

Let k be a field, U a smooth, affine, connected, unipotent, split and
nontrivial group over k, and a an action of a smooth affine group H on U.

1. Either k is infinite, or k satisfies `UnipotentSplitOver k` (module
   `Langlands.GroupScheme.Rational.SplitUnipotentStableCenter`). Mathlib's
   `finite_or_infinite k` splits into these cases. If k is finite, it is
   perfect (Mathlib instance `PerfectField.ofFinite`). The hypothesis then
   gives `UnipotentSplitOver k`.
2. The hypothesis `hvec` of
   `RationalDensity.splitUnipotentStableVectorSubgroup_of_isVectorGroup` is
   `isVectorGroup_of_isSplitUnipotent_of_exponent` of module
   `Langlands.GroupScheme.Rational.SplitCommutativeVector`. That theorem says
   that a commutative affine split unipotent group whose points are all killed
   by `ringChar k` is a vector group.
3. `RationalDensity.splitUnipotentStableVectorSubgroup_of_isVectorGroup`,
   applied to these two inputs, gives the conclusion for U, H and a. It does
   not use that H is smooth.
