# Finite-relative Hilbert 90

`Langlands.ClassFieldTheory.Local.FiniteRelativeH1Vanishing` asserts that
`relativeCohomology K L 1` is a subsingleton for every finite extension of
fields `L/K`. The two field carriers have independent universes. The group
is the actual automorphism group `Gal(L/K)`, and the coefficients are the
actual units `Lˣ`, written additively, with the published action over
`IntegerScalars = ULift ℤ`. No cohomology group or coefficient action is
changed.

This is a focused prerequisite for the finite-relative H¹ clause of
`CohomologyExistence`. It is stronger in its field hypotheses: no local
field, normality, separability, or chosen topology is needed. The
automorphism group can be smaller than the extension degree when the
extension is not Galois; the assertion still concerns that actual group.
There is no continuous absolute H¹ or H² claim in this statement.

The original source for the Galois case is Jean-Pierre Serre,
*Local Fields*, English translation by Marvin Jay Greenberg, GTM 67,
Springer, 1979, Chapter X, section 1, Proposition 2, printed page 150
(PDF page 156). The source proves that every multiplicative cocycle is a
coboundary by the linear independence of field automorphisms. Worker 80
read that original passage.

The extension to finite, possibly non-Galois field extensions is a derived
formulation. The same proof uses only the finite group of distinct
automorphisms. The pinned Mathlib theorem
`groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units`
already proves this elementary version for independent field universes.
The later proof of this target must connect that cocycle result to the
published lifted-scalar representation and its actual cohomology.
Mathlib's separate bundled `H1ofAutOnUnitsUnique` has carriers in
`Type 0` and does not by itself prove this target.

Source ID: `serre-1979-local-fields`. SHA-256:
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
Retained original:
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`.
The inspected Mathlib file is
`Mathlib/RepresentationTheory/Homological/GroupCohomology/Hilbert90.lean`
at revision `5ed2965256430c3649e86755f9576b54eca72435`.

This pair defines a proposition; it does not contain its proof.
