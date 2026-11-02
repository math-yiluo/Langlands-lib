# Actual adelic subgroup rational quotients

For a number field `F`, an actual group scheme `G/F`, and
`U : GroupScheme.SubgroupFunctor G`, this module evaluates `U` on `Spec F`
and on the actual full adele algebra. The inherited groups are respectively
`rationalPoints` and `adelicPoints`. The subgroup functor's restriction law
restricts the existing principal point homomorphism to `rational`. Its actual
image `rationalSubgroup` defines the left homogeneous quotient
`RationalQuotient`, with the existing quotient topology and positive right
translations.

`quotientInclusion` sends a subgroup class to its ambient rational class.
It is well defined, continuous, and commutes with positive right translation
by subgroup elements. The proof maps an actual principal-image witness
through subgroup inclusion, and then uses the quotient universal property.
The name denotes the induced map; injectivity is not asserted.

This is a derived construction from the existing actual point functor,
`SubgroupFunctor.comp_mem`, and `LeftCosetSpace`. It requires neither a
representing scheme for `U` nor a chosen replacement point model. It proves
no representability, rational-membership reflection, closedness, local
compactness, compactness, invariant measure, or finite-volume assertion
for the subgroup quotient. Such results need additional hypotheses and
proofs.
