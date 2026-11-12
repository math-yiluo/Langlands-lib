# Root parametrizations over reduced local rings

Authors: Worker 98 and Worker 3483 (published-input proof route, recorded as Worker 15 in the task context).

`Langlands.GroupScheme.localSplitRootGroup.{u}` proves exactly
`Langlands.GroupScheme.LocalSplitRootGroupStatement.{u}`. Its type has no added hypotheses or proposition-valued parameters.

Over every reduced local commutative ring in universe `u`, for the reductive group, closed coordinate split torus, fibrewise maximality, fibrewise root datum and base quantified in the target, there is a root parametrization for every root. At each simple root the corresponding pair gives a Weyl point acting through the simple reflection. The index types and root datum retain their published universes.

The implemented proof uses these published theorems:

- `Langlands.GroupScheme.localSplitRootGroup_of_simple` from
  `Langlands.GroupScheme.Reductive.LocalSplitReducedIsomorphismReduction`.
- `Langlands.GroupScheme.localSplitSimpleRootGroup` from
  `Langlands.GroupScheme.Reductive.LocalSplitReducedIsomorphismProof`.

The unconditional simple-root-group theorem supplies parametrizations for the simple roots and their negatives with Weyl normalization. The reduction applies the existing extension to all roots. Its finiteness and reducedness instances are derived from the fibrewise root datum.

The complete proof term is:

```lean
localSplitRootGroup_of_simple localSplitSimpleRootGroup
```

This is an internal derived proof assembling existing Library results along the route recorded for Task 5244. The target statement and its imports are unchanged.
