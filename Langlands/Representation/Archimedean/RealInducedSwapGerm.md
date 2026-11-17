# Target-valued regular families and inverse specialization

This internal unit uses algebraic projections, the explicit regularized
four-crossing maps, and finite-dimensional weak analytic calculus. It introduces
no topology on an ambient representation and no new continuation assumption.

`Admissible d e c` requires either total removed-denominator order zero, or
order one together with the explicit finite-support cancellation condition.
`regularMap` uses the raw family in the first case and the divided family
otherwise. Valid, admissible choices give weak analyticity for every fixed
input. Each such family's entire range lies in a finite-dimensional subspace.
At generic nonzero parameters, the family is exactly the actual generic shifted
raw map.

`targetRetraction` is an algebraic linear left inverse of the inclusion of the
actual target module in the expanded target. The inclusion is injective, so this
retraction is the identity on included target vectors. Composing with it gives
`regularTargetMap`, a linear map to the actual target for every parameter.
Weak analyticity survives composition with a fixed algebraic linear map; finite
ranges pass to their images. On the generic nonzero path the actual shifted map
already lands in the target, so the retraction leaves it unchanged. No
degree-layer bound or intertwining assertion is made for the projected family
at arbitrary parameters off that path.

The general `leftInverse_at_zero` theorem assumes a nontrivial filter finer
than the neighborhood filter at zero. It expands the varying input family
in a finite basis to prove analyticity of the composite. The eventual inverse
identity then specializes to zero by scalar continuity and dual separation.
Applying this theorem in both directions, with reverse parameter `-z`,
specializes the explicit generic inverse identities. `regularEquiv` packages
the resulting inverse linear maps between the actual induction modules.

The choices' validity and admissibility, and the existence of a nontrivial
generic path, remain explicit inputs. The file does not derive these choices
from unlinkedness or prove Lie intertwining. Thus the linear equivalence alone
does not prove `RealInducedSwapStatement`.
