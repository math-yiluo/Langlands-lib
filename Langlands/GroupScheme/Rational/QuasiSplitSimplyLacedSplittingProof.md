# Quasi-split groups with reduced simply-laced relative roots split

`Langlands.GroupScheme.quasiSplitSimplyLacedSplitting` proves the exact
published proposition
`Langlands.GroupScheme.QuasiSplitSimplyLacedSplittingStatement.{u}` at every
universe `u`. For every field `k`, quasi-split absolutely almost-simple group
scheme `G`, and actual maximal split torus `i : S.toGrp ⟶ G`, it proves
`HasReducedSimplyLacedRelativeRootSystem i → IsMaximalTorus i`.
The conclusion concerns the supplied torus and inclusion. There is no extra
premise, and no characteristic or perfectness restriction.

## Implemented proof

The proof applies the published
`quasiSplitSimplyLacedSplitting_of_relativeRootSystemIrreducible`.
It discharges that reduction's irreducibility premise directly with
`isIrreducible_fullRelativeRootPairing`, from
[`FullRelativeRootPairing`](FullRelativeRootPairing.md). Almost-simplicity
supplies the affine structure morphism needed to form the actual relative
roots. The given maximal split torus, nonempty root set and equality of the
entire root image are precisely the hypotheses of that theorem. The
evaluation-pairing hypothesis in the intermediate irreducibility proposition
is retained but is unnecessary for this stronger imported theorem.
No separate irreducibility theorem is assumed.

The imported
[`QuasiSplitSplittingReduction`](QuasiSplitSplittingReduction.md)
constructs a containing maximal torus `j : T.toGrp ⟶ G` and a finite Galois
extension splitting `T`. Absolute almost-simplicity persists over that
extension. The split maximal torus there has a nonempty actual root set,
and the published relative-root-system theorem constructs a pairing with
exactly that full root image. The irreducibility argument just supplied
makes this source pairing irreducible.

The original full-root predicate supplies the target pairing with symmetric
root-coroot pairings. Actual rational root restriction is surjective and
takes every source root to a target root. The published symmetric-pairing
criterion makes it injective. Galois transport preserves restriction, so
injectivity fixes every source root. Semisimplicity then fixes the whole
character lattice, and finite Galois character descent makes `T` split
already over `k`. Maximality of the supplied split torus makes its factor
into `T` an isomorphism. Transporting maximality of `j` gives
`IsMaximalTorus i` for the original inclusion.

## Provenance and scope

This is an internal composition of published Library results. Its mathematical
provenance and the arbitrary-field constructions are documented in the two
linked supporting modules and the target's
[`statement Markdown`](QuasiSplitSimplyLacedSplittingStatement.md).
The proof uses the entire relative-root set. It adds no folding table,
valuation, local-field, rank-one or simply connected hypothesis, and it uses
no local anisotropic classification or Kneser–Tits result.
