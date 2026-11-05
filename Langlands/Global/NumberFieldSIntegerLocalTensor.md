# Original local tensors of actual number-field S-integers

This derived construction supplies the actual global S-integer coefficients at
the original finite places for Conrad, *Weil and Grothendieck approaches to
adelic points* (2011), Example 4.2, printed pages 9–10. The lower exceptional
set S is any finite set of original finite places, and the upper exceptional
set is its full preimage under the original place restriction.

Write R for the actual lower S-integer ring and B for the actual upper
S-integer ring. At an original lower place p outside S, `lowerMap` is the
inclusion of R in the original local valuation ring inside K. Its membership
proof is exactly the outside-S valuation test. This local valuation ring is
proper. The previously proved Dedekind and fraction-field properties of R
therefore let `DedekindValuationOverring` construct its actual nonzero center
`centerPrime` on R and prove that the original local ring is the localization
at this center.

`localTensorEquiv` identifies the original local ring tensored with B over R
with its actual integral closure in the original upper field L. It specializes
`integralClosureLocalizationTensorEquiv` using the proved actual upper
S-integer normalization. The pure-tensor formula in L is the product of the
original lower field embedding and the original upper coefficient inclusion.

The R-algebra on the completed lower valuation ring is the composite of the
constructed lower local inclusion with the original local-to-completion
inclusion. Tensor cancellation, tensoring `localTensorEquiv`, and
`NumberFieldPlaceIntegralTensor.tensorEquiv` construct `completedTensorEquiv`.
It identifies the completed lower integer ring tensored with B over R with
the product of the original upper completed valuation rings over **all**
upper finite places above p. Its pure-tensor formula in each upper completion
is the original lower completion embedding times the original upper-field
coefficient map.

Every upper place above p lies outside the full exceptional preimage.
`upperMap` uses that membership fact to include B in the actual upper local
valuation ring and then its completion. The scoped upper coefficient algebra
is precisely this map. `completedTensorEquiv_one_tmul` proves that the right
tensor factor agrees with this original upper integral coefficient map.

All algebras and scalar towers used here are constructed inclusions or their
composites. The `Fact` premise states only p is outside S. K and L are original
number fields in an arbitrary common universe, with the given field
embedding. An empty finite-place S is allowed. No normalization or tensor
comparison is assumed. The scheme integral point homeomorphism and full
adelic Weil comparison remain obligations of the host task.
