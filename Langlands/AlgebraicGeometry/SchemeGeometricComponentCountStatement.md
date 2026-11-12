# Constructibility of every geometric component count for schemes

Author: Worker 107.

`SchemeGeometricComponentCountConstructibleStatement` is the scheme specialization of
Conrad's Lemma 5.1 (*Weil and Grothendieck approaches to adelic points*, December 31, 2011,
printed p.13; registered source `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`). Conrad's proof on that
page explicitly refers to the settled scheme case and EGA IV₃ 9.7.7. The formulation here
is derived by specializing the conclusion to schemes and spelling out its geometric
fibres using Mathlib schemes. This file states the result; it proves no constructibility
claim.

For a point `y` of an actual scheme `Y`, `componentCountGeometricPoint y` is
`Spec Ω ⟶ Spec κ(y) ⟶ Y`, where `Ω = AlgebraicClosure (Y.residueField y)`. The first map is
induced by the canonical field inclusion and the second is Mathlib's canonical
residue-field point. For `f : X ⟶ Y`, `geometricFiberComponentCount f y` is `ENat.card` of
the topological connected components of the actual scheme pullback along this point.
The value is in `ℕ∞`, and is `⊤` if there are infinitely many components.

The statement quantifies over every commutative ring `B`, every actual morphism of
schemes `f : X ⟶ Spec B` which is locally of finite presentation, quasi-compact and
quasi-separated, and every natural number `n`. The locus where the stated count is
`n` must be constructible in `Spec B`. No Noetherian hypothesis is imposed. Negative
integer counts in Conrad's wording give the empty locus, so only natural counts are
retained.

This target is a substantial prerequisite for the algebraic-space atlas argument.
The existing `GeometricallyConnectedFiberLocalConstructibility` addresses only the
geometrically connected locus, whereas this target covers every natural component
count. Comparing the scheme pullback here with the presheaf fibre and its point topology
in `AlgebraicSpace.GeometricFibreComponentsConstructibleStatement` requires additional
comparison results; it is not definitional equality and is not asserted in this module.
