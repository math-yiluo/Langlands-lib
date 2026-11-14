# All-field port of `Langlands.Representation.RankinSelberg.EqualRankTrilinearPrerequisites`

`Langlands.AllField.Representation.RankinSelberg.EqualRankTrilinearPrerequisites` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.EqualRankTrilinearPrerequisites`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Except for the changes described under Proof route below, each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.EqualRankTrilinearPrerequisites` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

Assembly from the exact representation-theoretic prerequisite statements.

## Proof route

The original rewrites the module topology to the supplied one (`topology_eq_canonicalModule`) before applying the finite-length hypotheses; the port applies the all-field hypotheses at the supplied `T` directly, so no rewriting is needed.

## Imports from the port

- `Langlands.AllField.Representation.Classification.FiniteLengthStatement`
- `Langlands.AllField.Representation.RankinSelberg.CentralBilinearVanishingProof`
- `Langlands.AllField.Representation.RankinSelberg.EqualRankFrobeniusStatement`
- `Langlands.AllField.Representation.RankinSelberg.FunctionalEquationStatementSupplement`
- `Langlands.AllField.Representation.RankinSelberg.MirabolicBilinearBounds`
- `Langlands.AllField.Representation.Whittaker.MirabolicFiniteLengthStatement`
- `Langlands.AllField.Representation.Whittaker.MirabolicPairingStatementSupplement`

## Declarations

- `Langlands.AllField.RankinSelberg.EqualRankTrilinearPrerequisites` (def): The named inputs to equal-rank trilinear uniqueness.
  The already-published central bilinear proof is not a missing input.
- `Langlands.AllField.RankinSelberg.mirabolic_pair_control_of_statements` (theorem): Functional multiplicity and pairing rigidity supply precisely the
  irreducible-pair control used in the finite-filtration bound.
- `Langlands.AllField.RankinSelberg.equalRankTrilinearUniqueness_of_prerequisites` (theorem): The exact named prerequisite statements imply the unchanged JPSS
  equal-rank target. Each input proof remains an explicit premise.
