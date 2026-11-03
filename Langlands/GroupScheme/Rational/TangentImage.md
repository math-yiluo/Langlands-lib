# Intrinsic tangent submodules and exact Lie images

This is derived internal infrastructure for the existing all-test subgroup
functors, dual-number identity kernels, and intrinsic action weights. It does
not invoke a new external structural theorem. All universes are arbitrary.

The module reuses the published `Lie.targetMap` and `Lie.targetMapLinear`
from `Rational.SplitTorusFiniteRank`. They give postcomposition by an actual
group-scheme homomorphism on identity-kernel points and its linear map for
affine source and target. The epsilon-scaling compatibility is recorded as
an interface lemma. Injectivity for monomorphic scheme maps is the published
`Lie.targetMapLinear_injective`.

`tangentSubmodule F` consists of the actual dual-number identity-kernel points
which belong to F on the dual-number test scheme. Addition is the existing
point-group law. Scalar closure follows from F's restriction law applied to
the algebra map that scales epsilon; representability is unnecessary.
The construction preserves inclusions, intersections, top and bottom.

The existing `HasLieImage F W` predicate is equivalent to the equality
`tangentSubmodule F = W`. This yields uniqueness and monotonicity of exact
Lie images. For a monomorphic map j with affine source and target,
`tangentSubmodule (SubgroupFunctor.range j)` is exactly the range of
`Lie.targetMapLinear j k`. To prove the nontrivial inclusion, lift a tangent
point through j and cancel j after reduction to show that the lift belongs
to the source identity kernel. The same comparison applies to any subgroup
functor represented by j.

The intrinsic action weight spaces agree with the existing differential
weight spaces for the identity map of the acting commutative group scheme.
Stability of F on all tests implies stability of its tangent submodule under
the differential at every ground-field point of the acting group. A character
belongs to `actionWeightSupport b F` exactly when its weight space has nonzero
intersection with `tangentSubmodule F`. An exact Lie image can therefore
replace the tangent submodule in this description.

These comparisons do not assert smooth representability, a weight
decomposition, subgroup uniqueness from Lie data, or semigroup realization.
