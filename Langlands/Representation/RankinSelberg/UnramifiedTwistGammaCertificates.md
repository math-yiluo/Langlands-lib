# Complete fixed-functional gamma certificate transport

This internally derived module transports a supplied equal-rank or unequal-rank gamma equation under two determinant character twists whose product is |·|ᵘ and which are separately trivial on −1. It asserts no initial existence of gamma factors.

`equal_equation` keeps the same model minus-one scalar and transports the nonzero rational witness through the injective rational rescaling equivalence. For every new coefficient-image vector, surjectivity of the actual `modelMap` supplies a common original carrier vector. The original equation supplies a Fourier partner and both continuations; the integral shifts transport them by +u and −u. The same Fourier partner is retained with its original measure and additive character. The scalar `GammaFunctionalEquation.shift` identifies reflection of the dual parameter with 1−(s+u).

`unequal_equation` performs the same construction for every rectangular decomposition j,k and its rank equality. Every decomposition retains its nonzero witness and both full model-vector quantifiers. The dual integral uses the actual complementary k-block, rectangular measure, and right Weyl translation proved in `UnramifiedTwistGammaIntegrals`.

Both statements retain independent field and two carrier universes. They impose no irreducibility, Whittaker-type, selected-functional, measure-existence, or multiplicativity hypothesis. The original functional equation conventions are those of JPSS (1983), (2.7)(iii), pp.390–391; the proof is the internal algebraic transport of the published gamma-certificate definitions.
