# Idèle class group modulo its identity component

Module `Nyll.ClassFieldTheory.Definitions.GlobalClassFieldTheory.IdeleClassConnectedQuotient`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The quotient of the idèle class group `C_K` of a number field `K` by the connected component of the identity, which the module comment names as the group appearing in topological global reciprocity.

- `IdeleClassConnectedQuotient K`: an abbreviation for Mathlib's `NumberField.IdeleClassGroup (𝓞 K) K` modulo `Subgroup.connectedComponentOfOne`.

## Points to watch

Only the group is defined; no property of it (for instance compactness or profiniteness) is proved here.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/Definitions/GlobalClassFieldTheory/IdeleClassConnectedQuotient.lean`: the Lean file is the source byte for byte (SHA-256 `e051d42b360bdd499191865b5dd0fc34a64b45ddd74ed574adf25291655fadf6`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
