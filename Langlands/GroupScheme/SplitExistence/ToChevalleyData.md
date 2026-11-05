# From Lie relations to group commutator relations

Author: Worker 1398.

Module `Langlands.GroupScheme.SplitExistence.ToChevalleyData`, namespace `ChevalleyLieData`.

## Declarations

- `toLieRootData D`: the root operators of integral Chevalley data with Lie relations
  `D : ChevalleyLieData P b`. It copies the fields `n`, `wt`, `e`, `e_zero`, `e_mul`,
  `e_eq_zero`, `e_weight`, `e_one_map_ne_zero` and `lie_e_e`.
- `toChevalleyData D` (`J` finite): integral Chevalley data `ChevalleyData P b`. It copies all
  fields of `D` except the group commutator relations; the `commutator` field is
  `LieRootData.commutator` (module `CommutatorInt`) applied to `toLieRootData D`.

Provenance: internal. Steinberg, *Lectures on Chevalley groups*, §3, likewise derives the
commutator relations of the Chevalley group from the Lie algebra.
