# All-field port of `Langlands.Representation.GodementJacquet.WhittakerCosetSum`

`Langlands.AllField.Representation.GodementJacquet.WhittakerCosetSum` is the all-field port of the Library module `Langlands.Representation.GodementJacquet.WhittakerCosetSum`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.GodementJacquet.WhittakerCosetSum` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Finite coset sums over a compact subgroup**

A compact subgroup `K` of a topological group is a finite disjoint union of left
cosets of an open subgroup `K₀ ≤ K`. Hence the Haar integral over `K` of a
function that is invariant under right translation by `K₀` is a finite sum of
values times the mass of `K₀`. For `GL_(n+1)` of a `p`-adic field, every
full-matrix test function is invariant under right translation by some open
subgroup. See the paired Markdown.

## Imports from the port

- `Langlands.AllField.Group.GL.BlockIwahoriDefinitionsSupplement`
- `Langlands.AllField.Group.GL.BlockModulusSupplement`
- `Langlands.AllField.Group.GL.CompactOpenSupplement`
- `Langlands.AllField.Representation.GodementJacquet.Zeta`

## Declarations

- `Langlands.AllField.GodementJacquet.CosetSum.Padic.exists_nhds_matrixTest_rightInvariant` (theorem): A full-matrix test function is invariant under right multiplication by every
  element of some neighborhood of the identity.
- `Langlands.AllField.GodementJacquet.CosetSum.Padic.isCompact_integralSubgroup` (theorem): The integral subgroup `GL_(n+1)(O)` is compact.
- `Langlands.AllField.GodementJacquet.CosetSum.Padic.isOpen_integralSubgroup` (theorem): The integral subgroup `GL_(n+1)(O)` is open.
- `Langlands.AllField.GodementJacquet.CosetSum.Padic.exists_openSubgroup_rightInvariant` (theorem): An open subgroup of `GL_(n+1)(O)` under which a full-matrix test function and
  a function on the group, right invariant under some open subgroup, are both
  right invariant.

Public declarations of the original that are not re-declared here: `Langlands.GodementJacquet.CosetSum.exists_finset_leftCosets`, `Langlands.GodementJacquet.CosetSum.exists_cosetSum`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
