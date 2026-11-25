# The three torus-filtration clauses over `K = F^ur` in the convention of `KPLocalMoyPrasadGroups`

These composition helpers are used by `KPQuasiSplitLocalTorusFiltrationProof`.

Lean module: `Langlands.Geometry.Building.KPLocalCentralizerTorusFiltrationClauses`.

The Library module `KPLocalMoyPrasadGroups` presents the torus `Z` by the single
binder `hZ : IsTorus B.centralizer.Z`. It defines `Z(K)_r = B.centralizerTorusFiltration hZ r`
and `j(Z(K)_r) = B.centralizerTorusImage hZ r`. Clause 3 for this filtration,
`centralizerTorusImage_isNormalizerStable`, is imported from the published module
`KPLocalCentralizerFiltrationNormalizerStable`. Clauses 1 and 2 are in the supporting modules
`KPLocalCentralizerFiltrationCommutatorFriendly` and `KPLocalCentralizerFiltrationRootCompatible`.

## Declarations

- `centralizerTorusFiltration_clauses_of_coroot_of_torusRoot hZ hcor hroot` assumes
  `KPLocalCorootComponentStatement` and `KPLocalTorusRootCommutatorStatement`. It states
  the three clauses of `QuasiSplitLocalTorusFiltrationStatement` for the filtration of
  `KPLocalMoyPrasadGroups` as one conjunction:
  clause 1 in the form of `IsCommutatorFriendly`, clause 2 in the form of `IsRootCompatible`,
  and clause 3 in the form of `IsNormalizerStable`. Proof: the triple of
  `centralizerTorusFiltration_isCommutatorFriendly_of_coroot`,
  `centralizerTorusImage_isRootCompatible_of_torusRoot` (whose depth-`0` case uses neither
  assumption) and `centralizerTorusImage_isNormalizerStable`.
- `quasiSplitLocalTorusFiltration_of_coroot_of_torusRoot hcor hroot`, in namespace
  `Langlands.Geometry.Building`: the same two assumptions imply the published statement
  `QuasiSplitLocalTorusFiltrationStatement` (KP Lemma 7.2.3 over `K`, Library module
  `KPQuasiSplitLocalTorusFiltrationStatement`). Its three conjuncts are
  exactly the three clauses above, so the proof introduces `F`, `H`, `B`, `hZ` and applies
  `centralizerTorusFiltration_clauses_of_coroot_of_torusRoot`. The final module
  `KPQuasiSplitLocalTorusFiltrationProof` applies this theorem to the published proofs
  `kpLocalCorootComponent` and `kpLocalTorusRootCommutator`, obtaining the exact
  unconditional statement `QuasiSplitLocalTorusFiltrationStatement`.

## Provenance

These helpers internally assemble the three published target clauses. The commutator
clause is Kaletha–Prasad (2023), Definition 7.2.1 and Lemma 7.2.3 (printed pp.245–246);
root compatibility and normalizer stability are additional derived clauses. The source
scope is documented in `KPQuasiSplitLocalTorusFiltrationStatement.md`, and the paired
Markdown of each clause helper describes its implemented proof.
