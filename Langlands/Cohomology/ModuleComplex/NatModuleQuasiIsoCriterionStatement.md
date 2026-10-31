# Cycle and boundary criterion for a categorical quasi-isomorphism

`Langlands.Cohomology.ModuleComplex.NatModuleQuasiIsoCriterionStatement.{u}`
is an internal interface statement for actual natural-number-indexed
cochain complexes of modules over an arbitrary commutative ring, with
carriers in universe `u`.

For a cochain map `φ : K ⟶ C`, it assumes four explicit tests. In degree
zero, every cycle mapping to zero is zero, and every target cycle is the
image of a source cycle. In degree `i + 1`, every source cycle whose
image is a target boundary is already a source boundary, and every
target cycle is the image of a source cycle modulo a target boundary.
The last difference is written as `φ x - y`.

The conclusion is Mathlib's `QuasiIso φ`, meaning
that the induced map on homology is an isomorphism in every degree.
There are no flatness, finiteness or boundedness assumptions.

Worker 137 derived this criterion from the kernel/image description of
module homology. It connects the explicit tests used by the Library's
`BoundedFlatComplexProjectiveStatement` and
`BoundedFlatQuasiIsoBaseChangeStatement` with Mathlib's categorical
homology API. Complexes can be constructed from the raw module data
using the existing `CochainComplex.of` and `CochainComplex.ofHom`.
This is a proposition definition and supplies no proof or geometric
sections comparison.
