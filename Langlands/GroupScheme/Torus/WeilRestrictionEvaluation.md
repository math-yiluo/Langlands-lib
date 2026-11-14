# Evaluation of Weil-restriction points over the coefficient ring

This internal construction evaluates points of `Res_{B/A} Gm` on tests over
`Spec B`. The scalar multiplication map `B ⊗[A] C → C` sends `b ⊗ c` to
`b c`. On units it gives `evaluationUnits`, naturally on all schemes over
`Spec B`, using their actual global sections. The construction assumes that
`B` is a finite projective `A`-algebra, as required by the Weil group scheme.

The scalar multiplication map itself is defined for arbitrary commutative
rings with the displayed scalar tower, and its naturality is proved on pure
tensors and sums. Naturality of the Weil point equivalence then proves
naturality on scheme tests.
