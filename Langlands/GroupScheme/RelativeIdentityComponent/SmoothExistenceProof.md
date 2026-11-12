# Proof of `Langlands.GroupScheme.RelativeIdentityComponent.SmoothExistenceStatement`

This module proves the published proposition `Langlands.GroupScheme.RelativeIdentityComponent.SmoothExistenceStatement` (module `Langlands.GroupScheme.RelativeIdentityComponentStatements`) at every universe `u`. The statement says that for every scheme `S` and every smooth group scheme `G` over `S`, a relative identity component `i : H ⟶ G` exists, with `H` smooth with geometrically connected fibres.

The theorem is `Langlands.GroupScheme.RelativeIdentityComponent.smoothExistence : SmoothExistenceStatement.{u}`, with no hypotheses.

## Proof

The proof term is the first component of the published conjunction `RelativeIdentityComponent.smoothStructure : RelativeIdentityComponent.SmoothStructureStatement` (projection `.1`).

The theorem adds no mathematics; it names a combination of published results.

## Published inputs

- `Langlands.GroupScheme.RelativeIdentityComponent.smoothStructure` (module `Langlands.GroupScheme.RelativeIdentityComponent.SmoothProof`)
