# All-field port of `Langlands.Representation.Whittaker.JPSUniformDilationProof`

`Langlands.AllField.Representation.Whittaker.JPSUniformDilationProof` is the all-field port of the Library module `Langlands.Representation.Whittaker.JPSUniformDilationProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Whittaker.JPSUniformDilationProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Proof of uniform small-coordinate dilation for actual JPS function spaces**

From the open norm-one subgroup of uniform coordinate-unit invariance, a basis of
the finite coordinate operator span made of bounded dilations gives the finite
functions and operators, and the published uniform-region recurrence for powers of
the uniformizer gives one threshold for all `|b| ≤ 1`. See the paired Markdown for
the route.

## Imports from the port

- `Langlands.AllField.Representation.Whittaker.JPSBoundedDilationRecurrenceProof`
- `Langlands.AllField.Representation.Whittaker.JPSCoordinateUnitInvarianceProof`
- `Langlands.AllField.Representation.Whittaker.JPSUniformDilationStatement`

## Declarations

- `Langlands.AllField.Whittaker.JPSUniformDilationProof.normalizedAbs_uniformizerUnit_pow_le_one` (theorem).
- `Langlands.AllField.Whittaker.JPSUniformDilationProof.normalizedAbs_uniformizerUnit_le_one` (theorem).
- `Langlands.AllField.Whittaker.JPSUniformDilationProof.exists_uniformizerUnit_pow_mul_normOne` (theorem): A bounded unit is a nonnegative power of the uniformizer times a norm-one unit.
- `Langlands.AllField.Whittaker.JPSUniformDilationProof.exists_finset_unit_cover` (theorem): Finitely many translates of an open subgroup cover the norm-one units.
- `Langlands.AllField.Whittaker.JPSUniformDilationProof.exists_bounded_operator_basis` (theorem): The finite operator span is spanned by bounded dilations, so it has a basis of
  operators `σ(β k)` with `|β k| ≤ 1`; `η` are the coordinates of `σ(b)` in it.
- `Langlands.AllField.Whittaker.JPSUniformDilationProof.uniformDilation_of_unitSubgroup` (theorem): The uniform dilation expansion for one actual space and coordinate, from the data of
  uniform coordinate-unit invariance and of the uniformizer recurrence.
- `Langlands.AllField.Whittaker.JPSUniformDilationProof.jpsUniformDilation_of_unitInvariance_of_recurrence` (theorem): Uniform coordinate-unit invariance and the uniform-region recurrence for powers of a
  bounded coordinate dilation imply uniform small-coordinate dilation.
- `Langlands.AllField.Whittaker.jpsUniformDilation` (theorem): Uniform small-coordinate dilation for actual JPS function spaces, from the
  published proofs of uniform coordinate-unit invariance and of the uniform-region
  recurrence for powers of a bounded coordinate dilation.
