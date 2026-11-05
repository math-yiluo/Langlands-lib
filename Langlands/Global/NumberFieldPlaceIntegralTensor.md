# Original local integral-closure tensor at a number-field place

This derived construction supplies local coefficient infrastructure for Conrad,
*Weil and Grothendieck approaches to adelic points* (2011), Example 4.2,
printed pages 9–10. It connects the actual local integral closure to the
published completed tensor of the original global rings of integers.

For an original finite place p of a number field K, `localRing` is the actual
valuation subring `valuationSubringAtPrime K p`, inside K. `completionMap`
restricts the original K-to-completion map to the actual completed valuation
ring. Its membership proof uses equality of the completed valuation with the
original valuation on K. The original global integer action factors through
this map, as proved by `completedTower`.

For an original upper number field L with its given K-algebra, `closure` is
the actual integral-closure subalgebra of this local ring in L. Each original
upper place q above p contains that closure. Indeed, the proved original-place
integrality comparison maps the lower local ring into the upper valuation
ring. Integrality then passes to the upper valuation ring, whose integral
closedness in the original L gives the desired membership. `closureMap` and
`upperMap` use this membership to restrict the original coefficient inclusions
to the upper original and completed valuation rings.

`tensorMap` multiplies the two original coefficient maps in each upper
completed ring. The scoped algebras and scalar towers are these explicit
inclusions. The pure-tensor formula is the original completion embedding of
the lower coefficient times the original L-to-upper-completion image of the
closure coefficient.

`localizationTensorEquiv` identifies the local ring tensored with the original
upper global integers with the actual local closure. This is a specialization
of the proved `integralClosureLocalizationTensorEquiv`, since the original
upper global integers are the integral closure of the original lower global
integers, and the original local ring is the localization at p.
`completedLocalizationEquiv` tensors this comparison with the completed lower
integer ring and cancels the intervening base change.

The comparison theorem proves that `tensorMap`, after this equivalence, equals
the published `AdelicFunctoriality.IntegralTensor.tensorMap`. Its proof uses
tensor induction: the pure-tensor case is the original coefficient formula,
and addition follows from the ring homomorphism laws. Bijectivity transfers
from the published original completed global-integer tensor equivalence.
`tensorEquiv` packages this result, retaining the original pure-tensor
formula and the exact upper coefficient map on the right tensor factor.
All original upper places above p occur.

K and L inhabit an arbitrary common universe. Both are number fields, with the
given original field embedding; p is an actual height-one prime of the
original lower integer ring. No local tensor decomposition is assumed. The
actual global S-integer specialization, point topologies and full adelic Weil
comparison remain obligations of the host task.
