# Finite parameter subgroup cardinality target (M363.003)

`Langlands.NYLL.LubinTate.standardLubinTateUnitParameterSubgroup_natCardStatement`
is the Prop-valued target of NYLL M363.003. For `{K : Type u} [Field K]`,
it takes explicit `F : LocalField.{u,v} K`, implicit
`π : F.valuationSubring`, an explicit proof that `π` is a uniformizer,
explicit naturals `n k` and bounds `1 ≤ k` and `k ≤ n + 1`, in source
order. It asserts
`Nat.card (standardLubinTateUnitParameterSubgroup F n k) =
Nat.card F.residueField ^ (n + 1 - k)`.

Both independent universes and all hypotheses are retained, including
the proof arguments that do not occur in the proposition body. This
pair states the target and supplies no proof. In particular, the target
alone does not establish finiteness or calculate the cardinality.
The sole import is the shared finite-parameter subgroup definition.

## Source and modifications

Original source: Naganori Yamaguchi, NYLL
`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/FiniteParameterFiltration.lean`,
pinned commit `fbd320cd8b1b06487c58227e92eb135794267709`,
M363.003, lines 62–117; signature and conclusion at 62–69,
section/universe context at 23–29. File SHA-256:
`0205d0dc5727b940c1ca25159ddc4ba008423ec44a19e8d7ae024a8a9f6e1aa1`.
Registered source `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

Worker 299 extracted the statement, prefixed the namespace with
`Langlands.NYLL`, suffixed the name with `Statement`, replaced the theorem
by a Prop-valued definition and renamed its unused proof binders to
`_hπ`, `_hk` and `_hkn`. The import is the focused shared definition
module. No hypotheses or instances are added. Original copyright and
author headers remain; `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`
retain the Apache-2.0 license and attribution.
