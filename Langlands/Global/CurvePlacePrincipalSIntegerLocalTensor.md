# Original local tensors of actual curve S-integers

This derived coefficient construction supports the integral point comparison in
Conrad, *Weil and Grothendieck approaches to adelic points* (2011), Example 4.2,
printed pages 9–10. It uses the actual cofinal principal exceptional sets and
their full upper-place preimages from `CurvePlacePrincipalSInteger`. All places,
fields, inclusions and completed valuation rings retain their original meanings.

Write R for the lower S-integer ring and B for the upper S-integer ring. Fix an
original lower place p outside S. `lowerMap` is the actual inclusion of R into
the original valuation ring at p, obtained from the outside-S membership
condition. The lower ring has already been proved Dedekind with the original
lower field as fraction field. `centerPrime` contracts the maximal ideal of
this proper valuation overring to R. The generic
`DedekindValuationOverring` construction proves that the original valuation ring
is the localization at this actual nonzero center.

`localTensorEquiv` now tensors the actual B with this localization. The previously
proved global integral-closure identification and
`integralClosureLocalizationTensorEquiv` identify the result with the integral
closure of the original local valuation ring in the original upper field.
Its pure-tensor formula, viewed in that field, is the product of the original
lower embedding with the original upper coefficient.

`completedTensorEquiv` tensors B instead with the original completed lower
valuation ring. Tensor cancellation first factors this through the original
local valuation ring. Tensoring `localTensorEquiv` and applying the proved
`CurvePlaceIntegralTensor.integralTensorEquiv` gives the product of the
original upper completed valuation rings over **all** upper places above p.
The formula for a pure tensor, viewed in each upper completion, is the original
completion embedding of its lower coefficient times the original upper-field
image of its upper coefficient.

Every such upper place lies outside the full exceptional preimage.
`upperMap` therefore includes B into that original upper valuation ring and
then into its completion. The scoped upper coefficient algebra uses exactly
this map. `completedTensorEquiv_one_tmul` proves that the right tensor
coefficient is precisely this upper coefficient algebra map.

The scoped algebras and scalar towers are the constructed inclusions and their
composites. The only additional `Fact` premises say that the chart denominator
is nonzero and that p lies outside the stated exceptional set. The lower field
is a function field over finite constants, is finite over the specified
parameter subfield, and the original upper extension is finite with compatible
constant-field structure. All fields share an arbitrary universe. No
separability hypothesis is used. The principal exceptional sets form the
previously proved cofinal family; arbitrary finite levels are not asserted
here. This is a coefficient-ring comparison; the scheme point topology and
adelic Weil comparison remain obligations of the host task.
