# The central maximal torus quotient of a Cartan subgroup

This derived construction works over every field of arbitrary universe.
`CentralMaximalTorusQuotientData` records a central maximal torus in an actual
group and an actual fppf quotient by its all-test image. The quotient is smooth,
connected and affine, and its projection is smooth. Every homomorphism from
any ground-field torus to the quotient has trivial all-test range. Nilpotence
and unipotence are not fields of these data.

`IsMaximalTorus.centralQuotient` constructs these data from a specified central
maximal torus of a smooth connected affine group. The existing normal-subgroup
quotient theorem supplies the quotient and its smooth affine structure.
Connectedness descends along the surjective projection. The existing
represented-kernel smoothness theorem makes the projection smooth. The
published central-maximal-torus quotient theorem supplies the absence of
nontrivial torus homomorphisms.

`IsCartanSubgroup.centralTorusQuotient` applies this construction to each actual
Cartan subgroup. The existing Cartan smoothness and connectedness theorem
provides its geometry; its closed embedding gives affineness. The original
witnessing maximal torus factors canonically through its represented
centralizer. Existing factorization results prove that this factor is both
central and maximal inside the Cartan. This construction assumes no geometric
nilpotence of the Cartan or the ambient group.

The projection has central scheme kernel by the fppf kernel-range equality.
If its quotient is unipotent, the companion central-extension module gives a
uniform lower-central-series bound on every scheme test, hence geometric
nilpotence. Applying the exact `NoTorusUnipotentStatement` to the quotient
therefore proves `cartanStructure_of_noTorusUnipotent`, whose conclusion is the
exact `CartanStructureStatement`.

The last theorem retains the entire no-torus unipotence statement as an
explicit hypothesis. It does not establish that hypothesis, unconditional
Cartan structure, or Cartan generation. All results are internal consequences
of the named Library constructions and the explicit conditional input; no
external source assertion is silently used.
