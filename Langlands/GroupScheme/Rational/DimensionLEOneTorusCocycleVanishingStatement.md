# Torus cocycle vanishing from the finite-extension norm criterion

`Langlands.GroupScheme.DimensionLEOneTorusCocycleVanishingStatement.{u}`
asserts that every field `K : Type u` satisfying the existing
`Langlands.FieldTheory.HasDimensionLEOne K` has
`Langlands.GroupScheme.HasTrivialTorusCocycles K`.

The field premise is the unchanged finite-extension norm criterion: for
every finite separable `E/K` and finite Galois `M/E` in `Type u`, the
actual determinant norm on units `Mˣ → Eˣ` is surjective. The conclusion
is the [actual torus Čech-cocycle property](TorusCocycleVanishing.md):
for every actual `K`-torus `T` and finite Galois `L/K`, every natural
scheme-valued cocycle on `Spec L → Spec K` is the coboundary of an actual
`L`-point of `T`. There is no premise of perfectness, prescribed
characteristic, supplied splitting isomorphism, or supplied trivialization.

This derived statement isolates the commutative cohomological
prerequisite in the dimension-one quasi-splitness proof. Serre,
*Galois Cohomology* (1997, corrected second printing 2002), Chapter III,
Section 2.2, proof of Theorem 1, printed pp.130–131/PDF pp.136–137,
step (4), reduces solvable-group vanishing to the torus case and cites
an earlier proof of that case. This passage assumes that the field is
perfect. Serre's official 2019 corrections, PDF p.3, change a
cross-reference on printed p.129 and an exercise on printed p.134;
they do not alter this passage.

The arbitrary-field reductive scope and the full norm criterion are
the ones in Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), Section 2.3 and Theorem
2.3.3(2), printed pp.78–79/PDF pp.109–110, including the imperfect-field
clarification after the theorem. Part (1) of that theorem asserts
vanishing of Galois `H¹` for every connected reductive group, and hence
in particular for tori. The present statement expresses that torus
consequence through the existing all-test-schemes Čech cocycles.
A proof must establish the comparison needed for this expression.
The official 1 November 2024 corrections, PDF pp.24–25, do not change
Section 2.3.

This module defines a proposition only. Torus-cocycle vanishing and the
structural passage from it to a field-defined geometric Borel remain
proof obligations. Worker 1333 authored this statement and explanation.
