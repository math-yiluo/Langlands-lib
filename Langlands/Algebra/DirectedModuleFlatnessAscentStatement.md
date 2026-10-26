# Eventual flatness ascends through a varying-ring directed colimit

`Langlands.Algebra.DirectedModuleFlatnessAscentStatement` is an internal
supporting proposition for the local flatness development. It asserts that,
for a `DirectedModuleSystem D` whose actual ring and additive colimit
comparisons are both bijective, eventual flatness of the component modules
over their component rings implies flatness of the specified target module
over the specified target ring.

Explicitly, the hypotheses are `D.IsColimit` and

```text
there exists i₀ such that, for every j with i₀ ≤ j,
  Module.Flat (D.base j) (D.obj j).
```

The conclusion is `Module.Flat R M`, with the target action already supplied
to `D`. The predicate `D.IsColimit` is the published conjunction of
bijectivity of `D.ringColimitMap` and `D.moduleColimitMap`, defined using
Mathlib's actual ring and additive direct limits. All transition maps,
semilinearity laws and cocone maps are those of the given `D`. The statement
introduces no alternative comparison or choice of module action.

The index `ι`, component rings, component modules, target ring `R` and target
module `M` have five independent universe levels `uI,uA,uN,uR,uM`.
The index is a nonempty directed preorder. No locality, finite type, finite
presentation, Noetherianity, tensor-transition, or injectivity of individual
transition maps is assumed.

This proposition is an internal mathematical consequence of the standard
equational criterion for flatness and the representative and eventual-zero
properties of directed colimits. It is not attributed to a separately numbered
source result. The intended proof lifts each finite relation to a stage,
makes it vanish at a later stage by injectivity of the additive comparison,
solves it at a subsequent flat stage, and maps the solution into the target.
The supporting APIs are Mathlib's `Module.Flat` and equational criterion,
`Ring.DirectLimit`, and `AddCommGroup.DirectLimit`, at the project's pinned
Mathlib revision. This file states that consequence without proving it.
It does not establish a local approximation existence theorem or the
local fibrewise flatness criterion.
