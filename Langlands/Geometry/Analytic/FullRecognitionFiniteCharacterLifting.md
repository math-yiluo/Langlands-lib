# Prescribed characters on finite full-recognition pairs

`HasFiniteCharacterLiftAt g y p` records a finite full-recognition chart pair
through a specified source point `y`, together with a bounded character on its
source chart. Its norm is the spectral point corresponding to `y`, and its
composition with the pair's pullback equals the prescribed target field
point's evaluation on that target chart.

`IsFiniteAt.hasFiniteCharacterLiftAt` proves this property whenever `g` is
finite at `y`, the underlying point of `p` is `g(y)`, and the coefficient
field `L` is complete, algebraically closed and ultrametric. The universe of
`L` is independent of those of the presentations and their chart algebras.
No Hausdorff or nontrivial-valuation condition is imposed.

The proof first selects a finite pointed pair using
`IsFiniteAt.hasFiniteFullRecognitionPairAt`. Admissibility places the
underlying point of `p` in the selected target chart. The chart compatibility
of the full-recognition pair system and injectivity of that target chart
identify the target spectral point of `p` with the comap of the selected
source spectral point. Consequently the prescribed target evaluation has
the norm required by `BanachSpectrum.exists_character_lift_of_finite`.
That theorem gives a bounded character with the source point's norm and
the required exact restriction to the prescribed target character.

This is an internal assembly of existing finite-pair selection and canonical
completed-residue character transport. It introduces no additional
identification with an external geometric construction. It supplies a
character on one finite source chart; extending it to compatible evaluations
on all charts and descending through the localized analytic category are
separate steps. This module alone does not prove geometric image lifting or
the point axioms of the étale site.
