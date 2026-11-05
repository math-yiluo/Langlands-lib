# Original completed-field tensors of actual S-integer coefficients

This derived construction supplies the field-valued local factors of the
actual S-integer Weil models in Conrad, *Weil and Grothendieck approaches to
adelic points* (2011), Example 4.2, printed pages 9–10.

The private coefficient helper cancels a base change and tensors a given
generic-fiber algebra equivalence. For an actual lower integer ring A, actual
upper integer ring B, original fields K and L, and original completed lower
field C, it takes the proved equivalence K tensored with B over A equals L
to an equivalence between C tensored with B over A and C tensored with L over K.
The pure tensor a tensor b is sent to a tensor the generic-fiber image of
1 tensor b. This formula follows from tensor cancellation and the tensor
congruence maps.

`NumberFieldSIntegerFieldTensor.tensorEquiv` composes this construction with
the published original completed-field tensor decomposition. It identifies
the actual upper full-preimage S-integer coefficients tensored with any
original lower finite-place completion with the product of all original
upper completions above it. `NumberFieldSIntegerInfiniteTensor.tensorEquiv`
does the same at every original infinite place, including real and complex
places. S is any finite set of original finite places, including empty.

`CurvePlacePrincipalSIntegerFieldTensor.tensorEquiv` gives the corresponding
comparison for the actual principal S-integer rings and their full upper
preimages in the function-field case. The previously proved cofinal principal
family uses the poles of a parameter and of the inverse of a nonzero
normalized-chart denominator. Its actual generic-fiber tensor equivalence and
the proved all-upper-place completed-field decomposition give the result.
Inseparable finite extensions are included.

In all three cases, the pure-tensor formula in each factor is the original
lower completion embedding times the original upper-field coefficient map.
The right pure tensor is exactly the original upper S-integer coefficient
algebra map. No outside-S condition is needed for any field-valued tensor.

At a finite place outside S, the scoped integral-to-field scalar towers also
prove compatibility of the constructed S-integer actions on the original
completed valuation rings with their original inclusions into the completed
fields, both below and at every upper place. These instances are direct
equalities of the already constructed coefficient maps.

All fields share an arbitrary universe. Number-field hypotheses and the
original field embedding are explicit. In the curve case the constants are
finite, the lower field has its original function-field presentation, it is
finite over the specified parameter subfield, and the original upper extension
is finite with compatible constant-field structures. The chart denominator
is nonzero. No desired tensor comparison is assumed. Scheme point topology,
integral-to-field point compatibility and the adelic Weil homeomorphism remain
obligations of the host task.
