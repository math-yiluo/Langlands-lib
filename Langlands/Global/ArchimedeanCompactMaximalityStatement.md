# Maximality of the standard archimedean compact subgroup

`Langlands.Global.StandardInfiniteCompactMaximalityStatement` is a proposition
definition parameterized by `K : Type u`, `[Field K]`, `[NumberField K]`, and
`n : ℕ`. The universe `u` is arbitrary. It states:

> For every subgroup `U` of `InfiniteAdelicGL K n`, if the carrier of `U` is
> compact and `standardInfiniteCompact K n ≤ U`, then
> `U = standardInfiniteCompact K n`.

The inclusion is ordinary subgroup inclusion and the conclusion is equality of
subgroups. The only assumptions on `U` are the displayed compactness and
inclusion. There is no positivity assumption on `n`, so rank zero is included.
This file defines a target for a separate proof; it does not prove maximality.

## Actual groups and topologies

`InfiniteAdelicGL K n`, imported from `Langlands.Global.AdelicGL`, abbreviates
`Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing K)`. The infinite
adele ring is the product of the actual completions `v.Completion`, indexed by
`v : NumberField.InfinitePlace K`. It has their product topology. Matrices have
the entrywise topology, and the general linear group has the existing units
topology, induced by the map recording a matrix and its inverse. `IsCompact`
refers to this topology on the actual ambient group; no replacement topology
or supplied topological-group model is introduced. The index type `Fin n` is
in `Type 0`; the field, its completion product, and the ambient group use the
single arbitrary universe `u`.

The imported `Langlands.Global.ArchimedeanCompact` constructs the specific
subgroup `standardInfiniteCompact K n` as the range of
`ArchimedeanCompactFactors.toInfiniteAdelicGL K n`. Its factors are
`Matrix.unitaryGroup (Fin n) ℝ` at real places and
`Matrix.unitaryGroup (Fin n) ℂ` at complex places. The former are the full
orthogonal groups, including both determinant signs when applicable. The
factors use their matrix subtype topologies and the product topology. Assembly
uses the inverse of the multiplicative homeomorphism
`archimedeanGLCoordinates K n` to land in the actual completion coordinates.
The real and complex identifications use Mathlib's existing choices for each
infinite place, including the representative embedding at a complex place.

The theorem `isCompact_standardInfiniteCompact K n` already proves compactness
of this very subgroup. The present definition records only the remaining
maximality clause. Together with that existing theorem, a proof of this
statement gives maximal compactness in the conventional sense. Compactness or
closedness alone does not establish the present assertion.

## Original source and derived scope

A. Borel and H. Jacquet, “Automorphic forms and automorphic representations,” in
*Automorphic Forms, Representations and L-Functions*, Proceedings of Symposia
in Pure Mathematics 33, Part 1 (1979), pp. 189–202, is the motivating original
source. The registered source is `borel-jacquet-1979-automorphic`; the retained
file is
`/home/taskhub/central-library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part I.pdf`,
SHA-256 `3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.

Section 1.1, printed p.189 (one-based PDF184), fixes a maximal compact subgroup
of the real reductive group. Section 1.4, printed p.190 (PDF185), uses `O(2, ℝ)`
in its `GL₂` example. Section 4.1, printed p.194 (PDF189), identifies the
archimedean group with the product of the groups over the infinite
completions. Section 4.2 begins on the same page by fixing a maximal compact
subgroup of that product, and its automorphic-form conditions continue on
printed p.195 (PDF190).

These passages specify the maximal-compact input to the automorphic theory.
They do not state or prove verbatim that the general-rank orthogonal/unitary
product constructed in the Library is maximal compact. The present proposition
is a derived structural target: specialize the source's archimedean group to
`GL_n`, choose the Library's concrete standard subgroup, and express the
remaining maximality obligation by quantifying over all compact overgroups.
This is the precise additional assertion needed to justify that choice in the
source's setting, rather than a consequence of the published compactness proof.
Its extension to `n = 0` is the formal empty-matrix convention; it is not
attributed to the source's examples.

The cited original pages and the central publication README were read. No
source-specific errata were present in the available project notes, literature
index, or retained publication folder. No conjugacy theorem, classification of
compact subgroups, or proof of the new target is claimed here.
