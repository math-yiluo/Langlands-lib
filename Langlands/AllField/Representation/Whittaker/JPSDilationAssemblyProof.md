# All-field port of `Langlands.Representation.Whittaker.JPSDilationAssemblyProof`

`Langlands.AllField.Representation.Whittaker.JPSDilationAssemblyProof` is the all-field port of the Library module `Langlands.Representation.Whittaker.JPSDilationAssemblyProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Whittaker.JPSDilationAssemblyProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**JPS decomposition assembly from uniform coordinate dilations: proof**

Coordinates are processed one at a time. A coordinate is either large, where it
stays in the coefficient, or small, where the dilation hypothesis replaces it by a
fixed unit and produces a translate of a finite function. After all coordinates
are processed, the coefficient is supported on a compact open box of the additive
space.

## Imports from the port

- `Langlands.AllField.HarmonicAnalysis.PadicScalarHaarScalingProof`
- `Langlands.AllField.Representation.Whittaker.JPSDilationAssemblyStatement`

## Declarations

- `Langlands.AllField.Whittaker.JPSDilationAssembly.normalizedAbs_pow` (theorem).
- `Langlands.AllField.Whittaker.JPSDilationAssembly.normalizedAbs_units_inv` (theorem).
- `Langlands.AllField.Whittaker.JPSDilationAssembly.exists_unit_normalizedAbs_lt` (theorem): Every positive bound is exceeded by the normalized absolute value of no power of a
  uniformizer beyond some exponent; in particular some unit lies below the bound.
- `Langlands.AllField.Whittaker.JPSDilationAssembly.freeze` (def): Replace the coordinates in `J` by those of `c`.
- `Langlands.AllField.Whittaker.JPSDilationAssembly.factor` (def): The factor of coordinate `i`: a small-ball cutoff times `γ i` on the frozen set `J`,
  the constant one on the unprocessed set `S`, and a large-coordinate cutoff otherwise.
- `Langlands.AllField.Whittaker.JPSDilationAssembly.term` (def): The function handled at one stage of the induction.
- `Langlands.AllField.Whittaker.JPSDilationAssembly.term_insert` (theorem): Processing one coordinate `i`: the large part keeps `g`, and the small part is
  expanded by the dilation formula at the frozen value `ci`.
- `Langlands.AllField.Whittaker.JPSDilationAssembly.term_induction` (theorem): The induction over the unprocessed coordinates `S`, for an arbitrary predicate `E`
  closed under sums. At every step the threshold of the dilation hypothesis is taken for
  the current function `g`, so no common choice over several functions is needed.
- `Langlands.AllField.Whittaker.JPSDilationAssembly.term_univ` (theorem): Every function is the term with all coordinates unprocessed.
- `Langlands.AllField.Whittaker.JPSDilationAssembly.isOpen_le` (theorem).
- `Langlands.AllField.Whittaker.JPSDilationAssembly.isClopen_le` (theorem).
- `Langlands.AllField.Whittaker.JPSDilationAssembly.isCompact_le` (theorem): Closed balls for the normalized absolute value are compact.
- `Langlands.AllField.Whittaker.JPSDilationAssembly.unitOf` (def): A unit with the given value, when the value is nonzero.
- `Langlands.AllField.Whittaker.JPSDilationAssembly.unitOf_val` (theorem).
- `Langlands.AllField.Whittaker.JPSDilationAssembly.val_unitOf` (theorem).
- `Langlands.AllField.Whittaker.JPSDilationAssembly.continuousAt_unitOf` (theorem).
- `Langlands.AllField.Whittaker.JPSDilationAssembly.fill` (def): The torus point with the coordinates of `J` taken from `c` and the others from `x`.
- `Langlands.AllField.Whittaker.JPSDilationAssembly.boxSet` (def): The admissible values of coordinate `i`: small on `J`, large off `J`.
- `Langlands.AllField.Whittaker.JPSDilationAssembly.box` (def): The box of all coordinates with admissible values.
- `Langlands.AllField.Whittaker.JPSDilationAssembly.isClopen_box` (theorem).
- `Langlands.AllField.Whittaker.JPSDilationAssembly.boxCoeff` (def): The coefficient of the terminal stage: `g` at the filled point on the box, zero off it.
- `Langlands.AllField.Whittaker.JPSDilationAssembly.boxCoeff_mem` (theorem).
- `Langlands.AllField.Whittaker.JPSDilationAssembly.term_empty_eq` (theorem): The terminal term is the box coefficient times a product of one-coordinate functions.
- `Langlands.AllField.Whittaker.JPSDilationAssembly.prodFun` (def): The product of one-coordinate functions over all coordinates.
- `Langlands.AllField.Whittaker.JPSDilationAssembly.transSpan` (def): The span of the constant one and of all left translates of members of `Y`.
- `Langlands.AllField.Whittaker.JPSDilationAssembly.one_mem_transSpan` (theorem).
- `Langlands.AllField.Whittaker.JPSDilationAssembly.translate_mem_transSpan` (theorem).
- `Langlands.AllField.Whittaker.JPSDilationAssembly.translate_mem_of_mem` (theorem): The span is stable under left translation.
- `Langlands.AllField.Whittaker.JPSDilationAssembly.continuous_of_mem_transSpan` (theorem).
- `Langlands.AllField.Whittaker.JPSDilationAssembly.fg_transSpan` (theorem).
- `Langlands.AllField.Whittaker.JPSDilationAssembly.prod_expand` (theorem): A product of one-coordinate functions from the spans of `B i` is a combination of
  products of members of the `B i`.
- `Langlands.AllField.Whittaker.JPSDilationAssembly.HasExpansion` (def): Expansion with Schwartz–Bruhat coefficients over products from the families `B`.
- `Langlands.AllField.Whittaker.JPSDilationAssembly.hasExpansion_zero` (theorem).
- `Langlands.AllField.Whittaker.JPSDilationAssembly.hasExpansion_add` (theorem).
- `Langlands.AllField.Whittaker.JPSDilationAssembly.hasExpansion_term` (theorem): The terminal terms have expansions.
- `Langlands.AllField.Whittaker.JPSDilationAssembly.isFiniteFunction_prodFun` (theorem): Products of members of the `B i` are finite functions on the torus.
- `Langlands.AllField.Whittaker.jpsDilationAssembly` (theorem): JPS (1979), Lemma (2.2.1), internal assembly step: one finite set of finite
  functions, chosen before the function, expands every function of the space with
  Schwartz–Bruhat coefficients on the whole additive space.
