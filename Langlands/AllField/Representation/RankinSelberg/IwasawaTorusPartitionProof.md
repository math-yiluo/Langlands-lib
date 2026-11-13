# All-field port of `Langlands.Representation.RankinSelberg.IwasawaTorusPartitionProof`

`Langlands.AllField.Representation.RankinSelberg.IwasawaTorusPartitionProof` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.IwasawaTorusPartitionProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). The original module does not name `PadicField` itself; the p-adic field enters through the statements that it proves or uses. In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.IwasawaTorusPartitionProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Proof of the measurable uniformizer-coset partition of the diagonal torus**

The valuation lemmas decompose every field unit uniquely as an integer power of
a uniformizing element times an integral unit. A group-theoretic lemma turns
such a decomposition, for a left-invariant measure giving the units mass one,
into the full coset partition of the finite product. The resulting countable
coset cover also supplies σ-finiteness of the normalized multiplicative Haar
measure.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.IwasawaTorusPartitionStatement`

## Declarations

- `Langlands.AllField.RankinSelberg.iwasawaTorusPartition` (theorem): The diagonal torus is the disjoint union of the measurable uniformizer cosets of its
  integral units, each of normalized product Haar mass one.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.valuation_eq_one_of_mem_integralUnits`, `Langlands.RankinSelberg.mem_integralUnits_of_valuation_eq_one`, `Langlands.RankinSelberg.zpow_eq_of_mul_integralUnits`, `Langlands.RankinSelberg.exists_zpow_mul_integralUnits`, `Langlands.RankinSelberg.sigmaFinite_of_zpow_cover`, `Langlands.RankinSelberg.zpow_coset_partition`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.
