# A splitting extension and intrinsic geometry of a torus

Worker 1357, with the scalar-map and descent proof pattern adapted from
Worker 866's published `QuasiSplitUnitaryReductiveProof` module.

This module supplies derived infrastructure over every field `k : Type u`,
in arbitrary characteristic. It uses the published definition `IsTorus T`,
which asserts that `T` becomes a finite split torus over some field extension.
It does not require that extension to be finite, algebraic or separable.

`TorusSplittingExtension T` packages such an extension as an actual field
with its `k`-algebra structure and the split-torus property after base change.
`IsTorus.splittingExtension` chooses this data from the existing existential
predicate. This choice adds no splitting theorem and supplies no claim that
the original torus is split over `k`.

`IsTorus.smooth` proves smoothness of the original structure morphism.
The chosen extension gives a smooth split torus by the published
`IsSplitTorus.smooth`. A field extension is faithfully flat, and its
map of spectra is surjective, flat and quasi-compact. Mathlib's
`MorphismProperty.of_pullback_snd_of_descendsAlong`, with the fpqc descent
instance for smooth morphisms, then descends smoothness.

`IsTorus.connectedSpace` uses the published connectedness of split tori.
The base-change projection onto the original torus is surjective, because
the scalar map is surjective. The continuous image of this connected
base change is the original underlying space, which is therefore connected.
Neither proof needs affineness of the original group as an additional premise.

`isSolvableGroupScheme_of_isCommMonObj` applies to every commutative group
scheme over `k`, with no smoothness or torus premise. Base change preserves
commutativity, so its geometric points form a commutative abstract group and
are solvable. This proves exactly the published geometric-point predicate
`IsSolvableGroupScheme`. In particular it applies to the commutative torus
sources used in the maximal-torus conjugacy target.

These are internal consequences of the existing definitions and imported
descent, split-torus and abstract-group results. Milne, *Algebraic Groups*
(2017), Definition 12.14 and the adjacent discussion on printed p.236
(PDF p.252), give the source definition of a torus and its smooth connected
interpretation. The implementation follows the descent argument above.
The retained 2017 errata do not correct that passage.

The field-extension fpqc calculation and the smoothness and connectedness
descent pattern follow the published
`Langlands.GroupScheme.Examples.QuasiSplitUnitaryReductiveProof` development.
Here they apply to the splitting extension in `IsTorus`, rather than to a
quadratic extension splitting a unitary group. No unitary-group theorem
or quadratic-extension hypothesis is imported.

The module does not prove Borel containment or conjugacy. It supplies
geometry needed to regard an actual closed torus embedding as a smooth
connected solvable subgroup in a later containment argument.

The field-extension fpqc fact is reused from the public
`Langlands.GroupScheme.fieldExtension_fpqc` in `BaseChangeReflection`.
