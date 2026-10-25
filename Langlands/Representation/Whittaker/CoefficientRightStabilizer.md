# Common compact open right stabilizers for actual coefficients

Author: Worker 408.

This internal adapter keeps two specified coefficient functions fixed and
chooses one compact open subgroup that fixes each under right translation.
The carrier universes of the two representations are independent.

## Definitions and hypotheses

`IsCommonCoefficientRightStabilizer f f' J` is a proposition asserting
`f(g*j)=f(g)` and `f'(g*j)=f'(g)` for every group element `g` and every
`j` in `J`. Here `f` and `f'` are elements of the actual coefficient images
of the specified equivariant functionals. The two subgroup characters may
be different. No existence is hidden in the predicate.

`exists_compactOpen_coefficientRightStabilizer` assumes a weakly locally
compact nonarchimedean group, two smooth representations over a commutative
ring, specified equivariant functionals, and specified coefficient vectors.
For every prescribed identity neighborhood `U`, it gives a compact open
subgroup contained in `U` satisfying that predicate. It does not assume
irreducibility, admissibility, nonzero functionals, or nonzero vectors.

## Implemented proof

The published `Whittaker.model_isSmooth` gives an open subgroup fixing each
coefficient vector in its actual image representation. Intersect the two
open subgroups with `U`, and apply `compactOpenSubgroupBasis`. Evaluate the
resulting fixed-vector equalities at an arbitrary group element. The image
action is the existing right-translation action, so evaluation gives the
two asserted pointwise equalities without changing either function.

`exists_compactOpen_glCoefficientRightStabilizer` specializes this argument
to the actual `GL_(n+1)` and opposite standard Whittaker characters over a
p-adic field. It uses every supplied `F.TopologicalData`, including rank one,
and installs the published supplied-topology nonarchimedean and local
compactness instances. The prescribed neighborhood is the open kernel of
`T.determinantNorm`; its openness is already proved for that supplied data.
Applying the generic construction and taking the real value of this
unit-valued character gives
`T.normalizedAbs (Matrix.det j.val.val) = 1` for every chosen subgroup element.
Thus no canonical-only topology or determinant normalization is substituted.

## Provenance and scope

This is an internal consequence of `Whittaker.Algebraic`,
`Topology.CompactOpen.NeighborhoodBasis`, `Group.GL.CompactOpen`, and
`Group.GL.NormalizedCharacter`; it introduces no new source theorem.
The standard characters and coefficient images are imported unchanged from
`Whittaker.GeneralLinear`. This module supplies a common right stabilizer
for already given coefficient functions. It constructs no compact mirabolic
tests or Kirillov lifts and proves no quotient-volume or parent equal-rank
unit-value existence statement. In particular no subgroup-normalization
condition is asserted.
