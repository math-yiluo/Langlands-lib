# Evaluation of realized vectors is homogeneous

This helper module declares one lemma about an operator realization `S` of `GL_n` over a
number field `F` (`Langlands.Automorphic.OperatorRealization`).

- `evaluate_toContinuous_smul`: for `c : ℂ`, a vector `f` of `S` and an adelic point `x`,
  the continuous function carried by `c • f` takes the value `c` times the value of the
  function carried by `f` at `x`. The proof is `map_smul` for the linear map
  `S.toContinuous`, followed by evaluation at `x`.

## Why the module exists

The same declaration `Langlands.Automorphic.OperatorRealization.evaluate_toContinuous_smul`,
with the same statement, used to appear in two modules:
`Langlands/Automorphic/CuspidalAdmissible/Reproduction.lean` and
`Langlands/Automorphic/OperatorScalarCentralCharacter.lean`. Lean rejects an environment
that contains the same name twice, so no module could import both files. In particular
`HenniartGlobalizationReduction` (which imports the first) and
`AssociatedCentralCharacterProof` (which imports the second) could not be used together.

Both copies are now removed, and both modules import this one. The name, the statement
and the namespace are unchanged, so every existing use still elaborates:
`Reproduction.lean`, `OperatorScalarCentralCharacter.lean` and
`IrreducibleCentralCharacterProof.lean` (which uses it as `S.evaluate_toContinuous_smul`).

The module imports only `Langlands.Automorphic.OperatorRealization`, where
`OperatorRealization.toContinuous` is defined. That file is not modified.

The lemma is internal infrastructure, not a result from the literature.
