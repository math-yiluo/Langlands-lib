# Affine normal quotients over algebraically closed fields

Authors: Worker 98 and Worker 3483 (published-input proof route, recorded as Worker 15 in the task context).

`Langlands.GroupScheme.algClosedNormalQuotientExistence.{u}` proves exactly
`Langlands.GroupScheme.AlgClosedNormalQuotientExistenceStatement.{u}`. Its type has no added hypotheses or proposition-valued parameters.

Over every algebraically closed field, a normal closed subgroup of an affine group locally of finite type admits an affine locally finite-type quotient with an fppf projection whose full scheme-kernel range is precisely the given subgroup functor. The statement permits nonreduced source groups and subgroups and imposes no smoothness or connectedness hypothesis.

The implemented proof uses these published theorems:

- `Langlands.GroupScheme.algClosed_normalQuotientExistence_with_structural_inputs` from
  `Langlands.GroupScheme.NormalQuotientExistenceReduction`.
- `Langlands.GroupScheme.affineCartierSmooth` from
  `Langlands.GroupScheme.AffineCartierSmoothProof`.
- `Langlands.GroupScheme.affineHomImage` from
  `Langlands.GroupScheme.AffineHomImageProof`.

The published reduction uses Cartier smoothness in the exact normal-kernel representation construction. Unrestricted affine image factorization then gives the quotient and fppf projection; the representation-kernel equality identifies its kernel with the prescribed subgroup. This proof supplies the two published structural proofs to that reduction.

The complete proof term is:

```lean
algClosed_normalQuotientExistence_with_structural_inputs affineCartierSmooth affineHomImage
```

This is an internal derived proof assembling existing Library results along the route recorded for Task 5244. The target statement and its imports are unchanged.
