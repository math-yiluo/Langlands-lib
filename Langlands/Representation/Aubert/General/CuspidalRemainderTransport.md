# Actual cuspidal remainder splittings under group equivalences

Authors: Workers 1553 and 321 (coordinated extraction interfaces and proof route).

This is an internal transport component for actual cuspidal-factor extraction.
It transports a supplied splitting and does not prove splitting existence.

`Langlands.SmoothRep.pullbackEquivalence` uses the published same-carrier
pullback functor in both directions. The unit and counit are identity linear
maps, supplied by the existing `Langlands.SmoothRep.pullbackSymmIso`;
their equivariance follows from cancellation of the group equivalence.

`HasCuspidalRemainderSplitting.pullback` assumes an equivalence of the precise
cuspidality predicates on all source objects. It pulls back the two objects
and the legs of the actual coproduct. The categorical equivalence preserves
that coproduct. For any nonzero subquotient of the pulled-back remainder,
inverse pullback gives a nonzero actual subquotient of the original remainder.
The assumed cuspidality comparison and the identity carrier isomorphism
transfer its cuspidality, contradicting the original remainder condition.
There is no irreducibility, admissibility or finite-length hypothesis.

The proof uses only actual smooth subquotient transport, the existing
cuspidality invariance under isomorphisms, and Mathlib's preservation of
colimits by categorical equivalences. No geometric lemma, adjointness,
classification, or splitting-existence theorem is used in these transport
constructions.

The full rational extraction target remains open. In particular, this component
does not construct an intrinsic rational cuspidal coproduct, prove connected
reductivity or a relative root system for an actual standard Levi, or build the
actual rational geometric filtration. The canonical rational-Levi application
will also require the published exact cuspidality-family comparison.
