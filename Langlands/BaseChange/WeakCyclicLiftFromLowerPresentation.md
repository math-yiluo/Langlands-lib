# Weak cyclic lift from a prescribed lower presentation

`weakCyclicLiftFromLowerPresentation` takes
`CuspidalCyclicBaseChangeLiftAnyDegreeStatement` as a premise. Fix a cyclic
extension of number fields with compact adelic quotients and all infinite
places split. The lower cuspidal spectral presentation has irreducible
admissible finite components. It has supercuspidal components at two
distinct split finite places and at the distinguished lower finite place,
where there is a unique upper place. The distinguished lower component is
given by a specified representation up to an unramified determinant twist.

A global norm-power twist makes the lower presentation have unitary
central character. Its finite components remain irreducible admissible
and the three supercuspidal components remain supercuspidal. The twist is
unramified at the distinguished place, where multiplication of the two
local twisting characters preserves the given form of the action.

Apply the cyclic lift premise to the unitary lower presentation and use
the weak spectral comparison and the lift identity at the unique upper
completion. The two definitions of the map from the distinguished
tensor to that completion are both the same projection of
`finiteTensorMap`. This gives `IsLiftAtDistinguishedTensor` for the actual
lower and upper components. These are the two lift properties needed
for the conductor reduction.
