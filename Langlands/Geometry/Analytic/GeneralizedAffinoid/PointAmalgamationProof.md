# Common complete-field realization of compatible affinoid points

Authors: Worker 125, Worker 972, and Worker 74.

`Langlands.Analytic.PresentedAffinoidAlgebra.pointAmalgamation` proves
the published `PointAmalgamationStatement` at every universe `u`.
For compatible points `x` of `B` and `y` of `C` over an actual presented
affinoid algebra `A`, it gives one complete ultrametric normed field
`L : Type u`, a `NormedAlgebra K L` structure, and bounded `K`-algebra
maps `f : B → L` and `g : C → L` satisfying

```text
f.comp i = g.comp j,
∀ b : B, ‖f b‖ = x b,
∀ c : C, ‖g c‖ = y c.
```

The Lean proof applies the published
`pointAmalgamation_of_completeFieldAmalgamation` to the unconditional
theorem `Langlands.Analytic.completeFieldAmalgamation`. Both imports
are instantiated at the same universe `u`; there is no remaining
amalgamation or tensor-seminorm hypothesis.

The completed-residue reduction in
`GeneralizedAffinoid.PointAmalgamationReduction` implements the passage
from fields to points. Let `z` be the common restriction of `x` and `y`
to `A`. The completed residue fields `H(z)`, `H(x)`, and `H(y)` are
complete ultrametric normed `K`-fields in `Type u`. The bounded maps
`i` and `j`, together with equality of the restricted points, induce
isometric bounded `K`-algebra maps from `H(z)` to `H(x)` and `H(y)`.
Field amalgamation gives commuting isometric bounded maps from these
last two fields into the same `L`.

The output maps `f` and `g` are their composites with
`completedResidueMap K x` and `completedResidueMap K y`.
Evaluating the field maps' commuting equation on the image of any
`a : A` in `H(z)` and using the completed-residue evaluation squares
gives `f (i a) = g (j a)`. Extensionality yields the stated equality
of bounded algebra maps. The two exact norm identities follow from
the field maps' isometries and `norm_completedResidueMap`.
Thus all three conclusions use the same maps, field, and coefficient
structure.

The imported field theorem in `ValuedField.AmalgamationProof` uses
the normalized ultrametric tensor seminorm, a dominated multiplicative
seminorm, and its realization in a complete ultrametric field.
Contractivity and the field inverse argument make the factor maps
isometric; the tensor relation makes them agree on their common field.
Its paired explanation supplies the details of that construction.

The result retains arbitrary positive polyradii, trivial valuations,
nonreduced and zero algebras, and empty spectra. In the empty-spectrum
case there are no input points to realize. No strictness,
rational-presentation, domain, nonzero, algebraicity or
spectral-injectivity hypothesis is introduced. The field stays in
`Type u`, including `u = 0`.

This is an internal derivation by composition of the imported Library
theorems, rather than a transcription of a numbered literature theorem.
Worker 74 supplied the completed-residue reduction and the source route;
Worker 972 contributed the tensor construction and final assembly;
Worker 125 assembled the field theorem and this exact point proof.
