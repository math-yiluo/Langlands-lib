# All-field port of `Langlands.Representation.Whittaker.MirabolicFiniteLengthProof`

`Langlands.AllField.Representation.Whittaker.MirabolicFiniteLengthProof` is the all-field port of the Library module `Langlands.Representation.Whittaker.MirabolicFiniteLengthProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Whittaker.MirabolicFiniteLengthProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Finite length of restriction to the actual mirabolic subgroup**

Bernstein--Zelevinsky (1976), Corollary 5.22, implication (1) implies (2).
Finite length over `GL_(n+1)` and finiteness of twisted coinvariants of
irreducible representations give finite-dimensional coinvariants for every
simple character `θ_S`. Detection then makes the total coinvariant dimension
a strictly monotone bounded function of mirabolic subrepresentations.

## Imports from the port

- `Langlands.AllField.Representation.Whittaker.IrreducibleCoinvariantFinitenessProof`
- `Langlands.AllField.Representation.Whittaker.MirabolicFiniteLengthDetection`
- `Langlands.AllField.Representation.Whittaker.MirabolicFiniteLengthStatement`
- `Langlands.AllField.Representation.Whittaker.MirabolicFunctionalTransfer`

## Declarations

- `Langlands.AllField.Whittaker.MirabolicFiniteLength.isLocallyConstant_selectedSum` (theorem): The upper-unipotent character `u ↦ ψ(∑_{S i} u_(i,i+1))` of `GL_(n+1)` is
  locally constant.
- `Langlands.AllField.Whittaker.MirabolicFiniteLength.isLocallyConstant_simpleCharacter` (theorem): The simple characters `θ_S` of the mirabolic upper-unipotent group are
  locally constant.
- `Langlands.AllField.Whittaker.MirabolicFiniteLength.isFiniteLength_of_finiteDimensional` (theorem): A smooth representation of `P_(n+1)` has finite length when all its
  simple-character coinvariants are finite-dimensional.
- `Langlands.AllField.Whittaker.MirabolicFiniteLength.of_irreducibleCoinvariantFiniteness` (theorem): BZ76 Corollary 5.22, (1) implies (2), from the finiteness of twisted
  upper-unipotent coinvariants of irreducible smooth representations (the
  finiteness part of BZ76 Theorem 5.21).
- `Langlands.AllField.Whittaker.mirabolicFiniteLength` (theorem): Bernstein--Zelevinsky (1976), Corollary 5.22, implication (1) implies (2):
  a smooth finite-length representation of `GL_(n+1)(F)` restricts to a
  finite-length representation of the actual mirabolic subgroup.

Public declarations of the original that are not re-declared here: `Langlands.Whittaker.MirabolicFiniteLength.isIrreducible_of_forall`, `Langlands.Whittaker.MirabolicFiniteLength.finiteDimensional_coinvariants_of_repLength_eq`, `Langlands.Whittaker.MirabolicFiniteLength.finiteDimensional_coinvariants_of_isFiniteLength`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.
