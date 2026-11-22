# Determination from common admissible local components

`nonempty_equivalence_of_common_admissible_localComponents` is a form of
`localComponentDetermination_reverse` for two irreducible operator
subquotients with a specified common admissible isotypic type at every
place. The finite-place input bundles irreducibility and admissibility
in `AutomorphicObject`. The real and complex inputs specify an
irreducible admissible local \((\mathfrak g,K)\)-module.

The proof uses these types for the commuting family of free-monoid
actions in `LocalComponentDeterminationReverse`. The local comparison
lemmas give scalar self-intertwiners and the required isotypy. At every
finite place the integral fixed vectors lie in a line by the spherical
fixed-space theorem. Only the finitely many infinite places can be
exceptions to the line condition. Then
`CommutingFamily.exists_linearEquiv_of_isotypic` gives an intertwining
linear equivalence of the space of each subquotient. The equivalence
intertwines every place generator, so `equivalenceOfPlaceComm` makes
it an equivalence for the full automorphic operator algebra.

The adapted proof uses the local admissibility of the supplied types
directly at the step where `localComponentDetermination_reverse`
obtains them from joint admissibility. Its provenance is the
restricted-tensor uniqueness argument of Flath (1979), §2, Example 2
and §3, Theorem 3 and the archimedean factors, pp. 181–182 (one-based
PDF pp. 177–178), and Getz–Hahn (2024), Theorem 6.3.7, pp. 165–166
(one-based PDF pp. 179–180).
