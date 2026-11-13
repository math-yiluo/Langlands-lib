# All-field port of `Langlands.Representation.Whittaker.MirabolicFiniteLengthCharacters`

`Langlands.AllField.Representation.Whittaker.MirabolicFiniteLengthCharacters` is the all-field port of the Library module `Langlands.Representation.Whittaker.MirabolicFiniteLengthCharacters`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Whittaker.MirabolicFiniteLengthCharacters` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Locally constant additive characters of a nonarchimedean local field**

Every locally constant character of the additive group of a nonarchimedean local
field `F`, with the topology and lattices of the supplied data `T`, is
`x ↦ ψ(a x)` for one fixed locally constant `ψ`, and every locally constant
character of `F^n` is `v ↦ ψ(a ⬝ᵥ v)`. A nonzero row can be moved to the last
coordinate row by an invertible matrix. These are inputs of the mirabolic
finite-length proof.

## Imports from the port

- `Langlands.AllField.HarmonicAnalysis.PadicLatticeTopology`

## Declarations

- `Langlands.AllField.Whittaker.MirabolicFiniteLength.additiveLattice_mul_mem` (theorem): Valuation lattices multiply additively in their indices.
- `Langlands.AllField.Whittaker.MirabolicFiniteLength.exists_mem_additiveLattice` (theorem): Every element lies in some valuation lattice.
- `Langlands.AllField.Whittaker.MirabolicFiniteLength.div_mem_additiveLattice` (theorem): Division by an element outside `L j` moves `L (c + 1)` into `L (c - j)`.
- `Langlands.AllField.Whittaker.MirabolicFiniteLength.exists_trivial_additiveLattice` (theorem): A locally constant character is trivial on some valuation lattice.
- `Langlands.AllField.Whittaker.MirabolicFiniteLength.exists_exact_conductor` (theorem): A nontrivial locally constant character has an exact conductor `t`: it is
  trivial on `L t` and nontrivial on `L (t + 1)`.
- `Langlands.AllField.Whittaker.MirabolicFiniteLength.mem_additiveLattice_of_forall_mul` (theorem): If `y ↦ ψ (a y)` is trivial on `L k`, then `a ∈ L (t - k)`.
- `Langlands.AllField.Whittaker.MirabolicFiniteLength.finite_quotient_additiveLattice` (theorem): Quotients of valuation lattices by smaller valuation lattices are finite.
- `Langlands.AllField.Whittaker.MirabolicFiniteLength.exists_mul_eq_on_additiveLattice` (theorem): On each lattice `L k` containing the triviality lattice `L m` of `χ`, the
  character `χ` agrees with `y ↦ ψ (a y)` for some `a ∈ L (t - m)`.
- `Langlands.AllField.Whittaker.MirabolicFiniteLength.exists_mul_eq` (theorem): Every locally constant character of `F` is `x ↦ ψ (a x)` for a fixed
  nontrivial locally constant `ψ`.
- `Langlands.AllField.Whittaker.MirabolicFiniteLength.exists_generating_character` (theorem): There is a locally constant character `ψ` of `F` such that every locally
  constant character is `x ↦ ψ (a x)`. If `F` has no nontrivial locally constant
  character, then `ψ = 1` works.
- `Langlands.AllField.Whittaker.MirabolicFiniteLength.exists_dotProduct_eq` (theorem): With a generating character `ψ`, every locally constant character of `F^n`
  is `v ↦ ψ (a ⬝ᵥ v)`.

Public declarations of the original that are not re-declared here: `Langlands.Whittaker.MirabolicFiniteLength.exists_eq_of_pairing`, `Langlands.Whittaker.MirabolicFiniteLength.exists_dotProduct_mulVec_eq_last`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.
