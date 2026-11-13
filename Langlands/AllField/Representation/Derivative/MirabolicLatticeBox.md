# All-field port of `Langlands.Representation.Derivative.MirabolicLatticeBox`

`Langlands.AllField.Representation.Derivative.MirabolicLatticeBox` is the all-field port of the Library module `Langlands.Representation.Derivative.MirabolicLatticeBox`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Derivative.MirabolicLatticeBox` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Lattice boxes and character sums for the radical of the mirabolic group**

Product lattices `(π^(-N) O)^k` in the radical coordinates `F^k`, finite character
sums over their quotients, and the duality of these boxes under `ψ`. They are used by
the `Φ⁻` irreducibility and pairing-transfer proofs.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.ZeroRowLastRowCutoffProof`

## Declarations

- `Langlands.AllField.Derivative.Mirabolic.latticeBox` (def): The box `(π^(-N) O)^k` of radical coordinates.
- `Langlands.AllField.Derivative.Mirabolic.mem_latticeBox` (theorem).
- `Langlands.AllField.Derivative.Mirabolic.latticeBox_mono` (theorem).
- `Langlands.AllField.Derivative.Mirabolic.coe_latticeBox` (theorem).
- `Langlands.AllField.Derivative.Mirabolic.isOpen_latticeBox` (theorem).
- `Langlands.AllField.Derivative.Mirabolic.isCompact_latticeBox` (theorem).
- `Langlands.AllField.Derivative.Mirabolic.exists_latticeBox_subset` (theorem): Every neighborhood of zero in the coordinate space contains a lattice box.
- `Langlands.AllField.Derivative.Mirabolic.finite_latticeBox_quotient` (theorem): The quotient of a lattice box by a smaller one is finite.
- `Langlands.AllField.Derivative.Mirabolic.inv_mem_additiveLattice_of_notMem` (theorem): An element outside `π^(-N) O` has inverse in `π^N O`.
- `Langlands.AllField.Derivative.Mirabolic.exists_ne_zero_mem_additiveLattice` (theorem): Every additive lattice contains a nonzero element.
- `Langlands.AllField.Derivative.Mirabolic.character_mul_eq_one` (theorem): `ψ(a x) = 1` for `a ∈ π^(-(n(ψ) - M)) O` and `x ∈ π^(-M) O`.
- `Langlands.AllField.Derivative.Mirabolic.character_dotProduct_eq_one` (theorem): `ψ(y ⬝ c) = 1` for `y` in the box at level `n(ψ) - M` and `c` in the box at level `M`.
- `Langlands.AllField.Derivative.Mirabolic.mem_latticeBox_of_forall_character_eq_one` (theorem): If `y ↦ ψ(y ⬝ c)` is trivial on the box at level `A`, then `c` lies in the box at
  level `n(ψ) - A`.

Public declarations of the original that are not re-declared here: `Langlands.Derivative.Mirabolic.sum_out_eq_zero`, `Langlands.Derivative.Mirabolic.eq_one_of_smul_eq_self`, `Langlands.Derivative.Mirabolic.continuous_of_forall_add_eq`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.
