# All-field port of `Langlands.Representation.Whittaker.MirabolicMinimalityProof`

`Langlands.AllField.Representation.Whittaker.MirabolicMinimalityProof` is the all-field port of the Library module `Langlands.Representation.Whittaker.MirabolicMinimalityProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

The original uses the canonical topological data `F.canonicalTopologicalData` of the p-adic field. The port uses the supplied data `T : LocalFieldData F` throughout. Where the original quantifies over a p-adic field with its canonical data, the port quantifies over a field `F` and arbitrary data `T`.

Source: the original module `Langlands.Representation.Whittaker.MirabolicMinimalityProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Proof of compact minimality in the actual mirabolic smooth induction**

The proof is by induction on the rank. For a nonzero subrepresentation `W` of the
smooth induction on `P_(m+2)`, restriction along `successor : P_(m+1) → P_(m+2)` gives
a nonzero subrepresentation of the smaller induction, which contains the compact
functions by induction. Finite character sums over the radical cut members of `W`
down to the points whose last row lies in a lattice box, and right translation by the
Levi moves such boxes around. A compactness argument then writes every compactly
supported function as a finite sum of such cut functions. See the paired Markdown.

## Imports from the port

- `Langlands.AllField.Representation.Derivative.MirabolicCharacter`
- `Langlands.AllField.Representation.Derivative.MirabolicLatticeBox`
- `Langlands.AllField.Representation.Whittaker.MirabolicMinimalityStatement`

## Declarations

- `Langlands.AllField.Whittaker.MirabolicMinimality.topologicalRing` (theorem).
- `Langlands.AllField.Whittaker.MirabolicMinimality.realized_cut` (theorem): Cutting a realized function by a lattice box of last rows keeps it realized.
- `Langlands.AllField.Whittaker.MirabolicMinimality.exists_cut_one` (theorem): Core step: near the standard last row, a compact function is cut into `W`.
- `Langlands.AllField.Whittaker.MirabolicMinimality.exists_cut_of_one` (theorem): Translation by the Levi moves the core step to every last row.
- `Langlands.AllField.Whittaker.MirabolicMinimality.mem_of_forall_cut` (theorem): Compactness: local cuts at every last row assemble the whole compact function.
- `Langlands.AllField.Whittaker.MirabolicMinimality.compactMinimality` (theorem): Compact minimality for every rank, for the supplied local-field data `T`.
- `Langlands.AllField.Whittaker.mirabolicCompactMinimality` (theorem): Bernstein–Zelevinsky (1976), Proposition 5.15(c), for the actual mirabolic smooth
  induction over every nonarchimedean local field `F`, with the topology of every
  supplied `T : LocalFieldData F`.

Public declarations of the original that are not re-declared here: `Langlands.Whittaker.MirabolicMinimality.ext_eval`, `Langlands.Whittaker.MirabolicMinimality.evalLinear`, `Langlands.Whittaker.MirabolicMinimality.evalLinear_apply`, `Langlands.Whittaker.MirabolicMinimality.exists_fix`, `Langlands.Whittaker.MirabolicMinimality.exists_eval_ne_zero`, `Langlands.Whittaker.MirabolicMinimality.Realized`, `Langlands.Whittaker.MirabolicMinimality.realized_of_mem`, `Langlands.Whittaker.MirabolicMinimality.mem_of_realized`, `Langlands.Whittaker.MirabolicMinimality.realized_congr`, `Langlands.Whittaker.MirabolicMinimality.realized_zero`, `Langlands.Whittaker.MirabolicMinimality.realized_add`, `Langlands.Whittaker.MirabolicMinimality.realized_sum`, `Langlands.Whittaker.MirabolicMinimality.realized_translate`, `Langlands.Whittaker.MirabolicMinimality.cut`, `Langlands.Whittaker.MirabolicMinimality.row_mul`, `Langlands.Whittaker.MirabolicMinimality.projection_mem_upperUnipotent`, `Langlands.Whittaker.MirabolicMinimality.eval_radicalElement_mul`, `Langlands.Whittaker.MirabolicMinimality.eval_mul_radicalElement`, `Langlands.Whittaker.MirabolicMinimality.res`, `Langlands.Whittaker.MirabolicMinimality.res_eval`, `Langlands.Whittaker.MirabolicMinimality.resLinear`, `Langlands.Whittaker.MirabolicMinimality.res_translate`, `Langlands.Whittaker.MirabolicMinimality.resRep`, `Langlands.Whittaker.MirabolicMinimality.resRep_ne_bot`, `Langlands.Whittaker.MirabolicMinimality.res_mem_compact`, `Langlands.Whittaker.MirabolicMinimality.eval_eq_of_res_eq`, `Langlands.Whittaker.MirabolicMinimality.mk_eq_mk_iff`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.
