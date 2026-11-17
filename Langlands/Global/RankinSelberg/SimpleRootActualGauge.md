# Symmetric Schwartz data as a gauge on actual adelic points

This internal transport lemma supports the common majorization prerequisite of
the unequal-rank Whittaker gauge tasks. It uses the supporting theorem
`exists_continuous_simpleRoot_extension`; it does not independently prove
Whittaker majorization or Mellin convergence.

`exists_actual_simpleRoot_gauge` takes a Schwartz–Bruhat function `Φ` on the
simple-root row and its `HasSimpleRootCoordinateSymmetries F c Φ`. It constructs
a continuous ENNReal-valued function `Ξ` on the actual adelic group-scheme
points, satisfying `IsAdelicSimpleRootGauge F r 0 Ξ`. On every upper triangular
matrix `b` followed by a standard compact matrix `k`, its value is the extended
norm of `Φ` at the simple-root row of the diagonal units of `b`. The result
retains every number field, universe and rank, including rank zero. It needs
no compactness assumption on the additive adelic quotient.

The preliminary private lemma proves continuity of Schwartz–Bruhat functions
by induction on their defining complex span. For a pure tensor, the
archimedean Schwartz function and finite locally constant function are
continuous, and the two coordinate maps are continuous. Addition and scalar
multiplication preserve continuity.

The main proof takes the continuous complex extension `Γ` supplied by the
matrix-group descent and defines
`Ξ(g) = ‖Γ(GeneralLinearGroupPoints.adelicEquiv F (r + 1) g)‖ₑ`.
The multiplicative homeomorphism `adelicHomeomorph` gives continuity and hence
measurability. The published `mem_unipotentAdelic_iff` identifies an actual
unipotent point with an upper unitriangular matrix, so the left invariance of
`Γ` transfers to `Ξ`. Right standard compact invariance transfers through the
definition of `gaugeStandardCompact`. Finally, applying the triangular-compact
formula to a diagonal matrix and the identity compact element gives the
torus formula. At exponent zero, the determinant-free simple-root weight is
one, as required by the published gauge definition.

The provenance is internal: the argument transports the named extension
through the published actual-group comparison and gauge definitions.
