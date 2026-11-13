# All-field port of `Langlands.Representation.RankinSelberg.ValuationShellIntegrationProof`

`Langlands.AllField.Representation.RankinSelberg.ValuationShellIntegrationProof` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.ValuationShellIntegrationProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). The original module does not name `PadicField` itself; the p-adic field enters through the statements that it proves or uses. In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.ValuationShellIntegrationProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Proof of the valuation-shell decomposition of multiplicative Haar integrals**

The specified uniformizer has order one. The order is a continuous homomorphism
from the units to the discrete integers, so the shells of fixed order are open,
disjoint and cover the units, and each is the translate of the order-zero
shell, which is the group of integral units. Left invariance of the normalized
Haar measure turns every shell integral into an integral over the integral
units, and the countable disjoint-union integral lemmas give the integrability
criterion and the integral identity.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.DeterminantSlices`
- `Langlands.AllField.Representation.RankinSelberg.ValuationShellIntegrationStatement`

## Declarations

- `Langlands.AllField.RankinSelberg.valuationShellIntegration` (theorem): The units of a nonarchimedean local field, with supplied data `T`, are the disjoint
  union of the valuation shells, each a uniformizer translate of the integral units of
  normalized Haar mass one, and the actual multiplicative Haar integral of a continuous
  function is the sum of its shell integrals.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.setIntegral_comp_mul_left_of_mem_iff`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.
