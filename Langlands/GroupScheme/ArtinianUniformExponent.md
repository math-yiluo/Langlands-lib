# Uniform exponents over Artinian local bases

Worker 801 develops the Artinian local restriction of the uniform exponent
argument in SGA 3, Exposé IX, Lemma 6.1 (registered source
`sga3-expose-ix-gille-polo-2009`, printed pp.52–53). The Prop-valued `Statement`
asks for one positive exponent on all scheme-valued points of a quasi-compact,
locally quasi-finite group scheme over an Artinian local base. It imposes no
flatness or commutativity assumption.

The internal helpers show that a finite reduced algebra over a
characteristic-zero field is formally unramified by decomposition into its
residue fields and separability. For a finite Hopf algebra over a local ring
with characteristic-zero residue field, the finite residue Hopf algebra is
reduced by the published characteristic-zero theorem. Base change of Kähler
differentials and Nakayama's lemma then give formal unramifiedness over the
original base. Coordinate choices are compared through their actual affine
presentations, and finiteness of the coordinate Hopf algebra is derived from
finiteness of the group scheme.

The statement itself remains a proof target. The omission of commutativity and
finite presentation is an internal strengthening of the Artinian local step: a
quasi-compact, locally quasi-finite morphism to an Artinian base is finite,
and a finite group over a field has a uniform exponent without commutativity.
This module proves only the stated algebra and coordinate helpers.

The coordinate comparison uses `AffineCoordinates.lieCoordinateAlgEquiv`. Finiteness uses `Diagonalizable.finite_hopfAlgebra`.
