# Isometric amalgamation of complete ultrametric fields

Author: Worker 74.

`Langlands.Analytic.CompleteFieldAmalgamationStatement` is a
Prop-valued interface for an internal analytic prerequisite. This module states
the assertion and supplies no proof.

Fix a universe `u`. The coefficient field `K : Type u` is complete and
ultrametric. The fields `E`, `F`, and `G` also belong to `Type u`; each
has a complete ultrametric field norm and a `NormedAlgebra K` structure.
The inputs are bounded `K`-algebra maps
`i : E → F` and `j : E → G` which are isometries.

The assertion supplies one field `L : Type u`, together with a normed field
structure, an ultrametric distance, completeness, and a `NormedAlgebra K L`
structure. It supplies bounded `K`-algebra maps `f : F → L` and
`g : G → L` with

```text
f.comp i = g.comp j,
Isometry f,
Isometry g.
```

All the existential structures govern the same field and both maps. The
commuting equation is equality of the actual bounded algebra maps from `E`
to `L`. Thus both maps agree on the given common field, respect the same
coefficient structure, and preserve their entire input norms.

No nontrivial valuation, algebraicity, separability, local compactness, or
spherical completeness assumption occurs. In particular, the fields may be
trivially valued. There is no universe enlargement, including at `u = 0`.

The provenance is internal and derived. This isolates the field assertion
needed to apply the published completed-residue construction to two compatible
spectrum points. Their completed residue fields and the common completed
base residue field supply `F`, `G`, and `E`; the published isometric maps in
`Spectrum.ResidueField.Lift` supply the input span. The interface does not
choose a tensor, valuation-ring, or spectrum-nonemptiness implementation,
and is not presented as a direct transcription of a numbered literature
theorem. Its proof and the subsequent application to affinoid points remain
separate obligations.
