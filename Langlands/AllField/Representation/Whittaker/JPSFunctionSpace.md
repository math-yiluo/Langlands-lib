# All-field port of `Langlands.Representation.Whittaker.JPSFunctionSpace`

`Langlands.AllField.Representation.Whittaker.JPSFunctionSpace` is the all-field port of the Library module `Langlands.Representation.Whittaker.JPSFunctionSpace`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Whittaker.JPSFunctionSpace` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**JPS function spaces and coordinate germs**

The actual function spaces and coordinate quotients in JPS (1979), Lemma
(2.2.1), with algebraic constructions separated from smoothness assumptions.

## Imports from the port

- `Langlands.AllField.LocalField.Foundation`

## Declarations

- `Langlands.AllField.Whittaker.JPSFunctionSpace.Torus` (abbrev): The multiplicative coordinate group, including the singleton group at `n = 0`.
- `Langlands.AllField.Whittaker.JPSFunctionSpace.FunctionSpace` (abbrev): An actual translation-stable complex subspace of functions on the coordinate group.
- `Langlands.AllField.Whittaker.JPSFunctionSpace.coordinateEmbedding` (def): Embed one multiplicative coordinate, setting every other coordinate to one.
- `Langlands.AllField.Whittaker.JPSFunctionSpace.coordinateEmbedding_apply` (theorem).
- `Langlands.AllField.Whittaker.JPSFunctionSpace.coordinateEmbedding_same` (theorem).
- `Langlands.AllField.Whittaker.JPSFunctionSpace.mul_coordinateEmbedding` (theorem): Multiplication by the embedding multiplies exactly the specified coordinate.
- `Langlands.AllField.Whittaker.JPSFunctionSpace.translate_apply` (theorem): Restricted translation still evaluates the actual underlying function at `a * s`.
- `Langlands.AllField.Whittaker.JPSFunctionSpace.coordinateRepresentation` (def): Coordinate translation on the original function space.
- `Langlands.AllField.Whittaker.JPSFunctionSpace.coordinateRepresentation_apply` (theorem).
- `Langlands.AllField.Whittaker.JPSFunctionSpace.HasCoordinateUpperSupport` (def): A bound may depend on the function and coordinate, but not on the other coordinates.
- `Langlands.AllField.Whittaker.JPSFunctionSpace.VanishesNearCoordinateZero` (def): Uniform vanishing near zero in coordinate `i`, on the multiplicative torus.
- `Langlands.AllField.Whittaker.JPSFunctionSpace.vanishesNearCoordinateZero_zero` (theorem).
- `Langlands.AllField.Whittaker.JPSFunctionSpace.vanishesNearCoordinateZero_add` (theorem).
- `Langlands.AllField.Whittaker.JPSFunctionSpace.vanishesNearCoordinateZero_smul` (theorem).
- `Langlands.AllField.Whittaker.JPSFunctionSpace.vanishesNearCoordinateZero_translate` (theorem): Every translation preserves near-zero vanishing; its threshold is rescaled by `|s_i|`.
- `Langlands.AllField.Whittaker.JPSFunctionSpace.coordinateVanishing` (def): The actual invariant subspace `W_i` inside `W`, not an arbitrary supplied subspace.
- `Langlands.AllField.Whittaker.JPSFunctionSpace.CoordinateGerm` (abbrev): The genuine algebraic coordinate-germ quotient `W / W_i`.
- `Langlands.AllField.Whittaker.JPSFunctionSpace.germRepresentation` (def): The full translation representation on the actual quotient.
- `Langlands.AllField.Whittaker.JPSFunctionSpace.germMap` (def): Canonical projection from functions to coordinate germs, as an intertwiner.
- `Langlands.AllField.Whittaker.JPSFunctionSpace.germMap_surjective` (theorem).
- `Langlands.AllField.Whittaker.JPSFunctionSpace.germMap_eq_zero_iff` (theorem).
- `Langlands.AllField.Whittaker.JPSFunctionSpace.germRepresentation_apply_mk` (theorem).
- `Langlands.AllField.Whittaker.JPSFunctionSpace.sigma` (def): JPS's coordinate action `σ_i` on this actual coordinate-germ quotient.
- `Langlands.AllField.Whittaker.JPSFunctionSpace.sigma_apply_mk` (theorem): Translating a germ amounts to taking the germ of the translated representative.
- `Langlands.AllField.Whittaker.JPSFunctionSpace.HasFiniteCoordinateOperatorSpan` (def): The finite-dimensional operator-span hypothesis, in the endomorphisms of `W / W_i`.
- `Langlands.AllField.Whittaker.JPSFunctionSpace.HasFiniteOperatorSpans` (def): The preceding hypothesis in every coordinate; vacuous at rank zero.
- `Langlands.AllField.Whittaker.JPSFunctionSpace.IsLocallyConstantSpace` (def): The locally constant interpretation of the source's smooth scalar-valued functions.
- `Langlands.AllField.Whittaker.JPSFunctionSpace.IsFiniteFunction` (def): The exact continuous translation-finite predicate, with the parent's `b * a` convention.

Public declarations of the original that are not re-declared here: `Langlands.Whittaker.JPSFunctionSpace.coordinateEmbedding_commute`, `Langlands.Whittaker.JPSFunctionSpace.coordinateRepresentation_apply_update`, `Langlands.Whittaker.JPSFunctionSpace.coordinateRepresentation_commute`, `Langlands.Whittaker.JPSFunctionSpace.mem_coordinateVanishing_iff`, `Langlands.Whittaker.JPSFunctionSpace.sigma_translate_commute`, `Langlands.Whittaker.JPSFunctionSpace.IsSmoothSpace`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.
