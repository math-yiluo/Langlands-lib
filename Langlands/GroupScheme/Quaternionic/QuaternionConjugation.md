# Quaternion conjugation from the original dimension assumptions

Authors: Worker 124.

This internal construction starts with the quaternionic target's actual
dimension hypotheses: the central division algebra has dimension four
over `K`, and the fixed space of its involution `σ` has dimension three.
Rank-nullity gives dimension one for its alternating subspace, in every
characteristic. A nonzero member is invertible in the division algebra;
`quaternionAlternatingUnit` chooses one such unit.

The actual involution `quaternionConjugation` twists `σ` by that unit,
using `AlternatingConjugation.alternatingTwist`. The dimension-square
formula for reduced degree gives reduced degree two, and the proved
alternating-norm comparison identifies the conjugate product of every
original element `a` with the scalar image of its canonical reduced norm.

Over an infinite ground field, the conjugate-product identity extends to
every commutative coefficient algebra, including nonreduced ones.
The proof uses the generic finite-basis element over a multivariate
polynomial ring. Every coordinate of its norm defect vanishes at all
ground-field assignments, so polynomial extensionality makes it zero.
Evaluation at the coordinates of any tensor element transports the
identity to the chosen coefficient algebra. The argument uses the
published naturality of tensor coordinates, the involution extension and
the actual reduced norm. The infinite-field hypothesis applies to this
extension step; it does not restrict characteristic.

The construction does not assert independence of the chosen alternating
unit, a spin group model or elementary generation in a spin group.
