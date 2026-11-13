# All-field port of `Langlands.Representation.Whittaker.SupercuspidalCoinvariantFinitenessProof`

`Langlands.AllField.Representation.Whittaker.SupercuspidalCoinvariantFinitenessProof` is the all-field port of the Library module `Langlands.Representation.Whittaker.SupercuspidalCoinvariantFinitenessProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Whittaker.SupercuspidalCoinvariantFinitenessProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Finite twisted upper-unipotent coinvariants of irreducible supercuspidal representations**

Proof of `Langlands.AllField.Whittaker.SupercuspidalCoinvariantFinitenessStatement`. Degenerate
characters give zero coinvariants. For a nondegenerate character the quotient is spanned by
the classes of finitely many torus translates of a finite-dimensional space of fixed vectors:
nondegeneracy kills translates by torus elements that expand a simple root too much, and the
vanishing of the Jacquet quotients kills those that contract one too much.

## Imports from the port

- `Langlands.AllField.HarmonicAnalysis.PadicAdditiveConductorProof`
- `Langlands.AllField.Representation.Derivative.MirabolicMinus`
- `Langlands.AllField.Representation.Whittaker.SupercuspidalCoinvariantFinitenessStatement`

## Declarations

- `Langlands.AllField.Whittaker.SupercuspidalCoinvariantFinitenessProof.uniformizer_ne_zero` (theorem).
- `Langlands.AllField.Whittaker.SupercuspidalCoinvariantFinitenessProof.uniformizerUnit` (def): The chosen uniformizer as a unit.
- `Langlands.AllField.Whittaker.SupercuspidalCoinvariantFinitenessProof.isUniformizingElement` (theorem): The chosen uniformizer is a uniformizing element for the actual valuation.
- `Langlands.AllField.Whittaker.SupercuspidalCoinvariantFinitenessProof.uniformizerUnit_zpow_val` (theorem).
- `Langlands.AllField.Whittaker.SupercuspidalCoinvariantFinitenessProof.exists_zpow_mul_mem` (theorem): Large powers of the uniformizer move any element into any lattice.
- `Langlands.AllField.Whittaker.SupercuspidalCoinvariantFinitenessProof.isTopologicalRing` (theorem).
- `Langlands.AllField.Whittaker.SupercuspidalCoinvariantFinitenessProof.continuous_adjacentUnit` (theorem).
- `Langlands.AllField.Whittaker.SupercuspidalCoinvariantFinitenessProof.conj_mem_principalLevelSubgroup` (theorem): A principal congruence subgroup is normalized by the integral group.
- `Langlands.AllField.Whittaker.SupercuspidalCoinvariantFinitenessProof.finite_of_nondegenerate` (theorem): For a nondegenerate character, the twisted coinvariants of an irreducible supercuspidal
  representation of `GL_(n+1)` are finite dimensional.
- `Langlands.AllField.Whittaker.supercuspidalCoinvariantFiniteness` (theorem): The finite-dimensionality part of BZ76 §5.18 for the actual twisted upper-unipotent
  coinvariants of an irreducible supercuspidal representation, for every locally constant
  character.

Public declarations of the original that are not re-declared here: `Langlands.Whittaker.SupercuspidalCoinvariantFinitenessProof.diagonalConj_adjacentUnit`, `Langlands.Whittaker.SupercuspidalCoinvariantFinitenessProof.character_diagonalConj_of_isBlockUnipotent`, `Langlands.Whittaker.SupercuspidalCoinvariantFinitenessProof.diagonalUnit_mul`, `Langlands.Whittaker.SupercuspidalCoinvariantFinitenessProof.diagonalUnit_const_commute`, `Langlands.Whittaker.SupercuspidalCoinvariantFinitenessProof.mk_diagonal_apply`, `Langlands.Whittaker.SupercuspidalCoinvariantFinitenessProof.mk_diagonal_eq_zero_of_adjacent`, `Langlands.Whittaker.SupercuspidalCoinvariantFinitenessProof.mk_diagonal_sub_eq_zero`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.
