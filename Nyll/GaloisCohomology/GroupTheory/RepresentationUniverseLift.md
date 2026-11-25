# Lifting a representation to the maximum universe

Module `Nyll.GaloisCohomology.GroupTheory.RepresentationUniverseLift`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a ring `R` and a monoid `G` in universe `uG`, representations whose carriers live in universe `uA` are moved to representations of `ULift G` with carrier in `max uG uA`, so that group and carrier share one universe.

- `Rep.universeLiftFunctor`: the functor `Rep R G ⥤ Rep R (ULift G)`, the composite of Mathlib's `ModuleCat.uliftFunctor` applied to the action with restriction along `MulEquiv.ulift`.
- `universeLiftFunctor_obj_V`, `universeLiftFunctor_obj_ρ_apply`, `universeLiftFunctor_map_apply`, `universeLiftFunctor_smul_down`: the carrier is `ULift A`, and the action, morphisms and scalar multiplication are the original ones under `ULift.up`/`down`, all by definition.
- Instances: the functor is additive and preserves finite limits and finite colimits.
- `universeLiftFunctor_shortExact`: it sends short exact sequences to short exact sequences.
- `universeLiftFunctor_norm_down`: for a finite group `K`, the norm map of the lifted representation is the original norm map after removing the lift.

No smallness hypothesis is used. The norm statement requires a group with a `Fintype` instance.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/GaloisCohomology/GroupTheory/RepresentationUniverseLift.lean`: the Lean file is the source byte for byte (SHA-256 `a4d57970859653b5ad58139f3e56ff529551e1f73f71f6a01d16299c62f497cd`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
