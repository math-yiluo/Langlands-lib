# Central isogenies reflect torus centralizers

Author: Worker 1614.

For a central isogeny `π : G ⟶ H` over any field and an actual torus
homomorphism `j : T ⟶ G`, this module proves that the inverse image of
the all-test centralizer of `j ≫ π` equals the all-test centralizer of
`j`. The membership theorem applies to every test scheme and every
point, including nonreduced schemes.

`CentralIsogenyTorusCentralizerReflectionStatement.{u}` packages this
assertion at an arbitrary universe. The theorem
`centralIsogenyTorusCentralizerReflection` proves it.

This is an internal consequence of the published kernel-exponent and
torus-multiplication theorems. No additional literature assertion is
introduced. A positive integer `N` kills the full central kernel on every
test scheme. If two points commute after `π`, their commutator is central
and killed by `N`; the first point therefore commutes with the `N`-th
power of the second. Multiplication by `N` on the torus is flat and
surjective. Pulling that map back along an arbitrary torus point gives
an epimorphic refinement on which the point has an `N`-th root.
Commutation after that refinement implies commutation on the original
test scheme.

The theorem does not assert that centralizers are represented, that the
ambient groups are reductive, or that a full torus preimage is a torus.
It supplies the all-test reflection step for the latter argument.
