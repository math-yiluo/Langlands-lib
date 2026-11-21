# Common normalization from continuation witnesses

`IsMeromorphicOn.exists_flat_numerator` starts with a meromorphic family
on an open subtype of the complex parameter space. It extends one
local numerator and denominator to the ambient space, using the
open-subtype comparison for each scalar test. In the local window the
regular points with nonzero denominator are open and dense by the
scalar identity theorem. The numerator agrees under the supplied
linear evaluation with the denominator times the original family
on those points.

`exists_common_normalization_of_meromorphic` applies this construction
to every basis section. It gives one ball, one open level, one growth
exponent and a common denominator. The weakly holomorphic family in the
common growth space evaluates at regular points to the product
denominator times `continuedLinearCombination` of the basis sections.

This is an internal bridge from the continuation witnesses in
Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*
(2024), §3.1 and Corollary 8.6, to the locally normalized holomorphic
families in Langlands, *On the notion of an automorphic representation*
(1979), printed pp. 205–207.
