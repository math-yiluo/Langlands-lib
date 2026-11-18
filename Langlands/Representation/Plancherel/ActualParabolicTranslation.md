# Translation from an arbitrary common-Levi parabolic

This module realizes formula (1) in Waldspurger, *La formule de Plancherel
pour les groupes p-adiques* (2003), V.3, printed p. 295, PDF p. 61. It uses
`ActualCommonLeviCoherence.ParabolicPresentation`, so the source parabolic
has the centralizer of the cocharacter presenting the Levi and can be
any parabolic with that common Levi and the displayed Iwasawa factorization.
The field and smooth representation carrier have independent universes.

`conjugatePresentation` takes the actual conjugate of the source
cocharacter in the target Levi. It uses the equality of the conjugated
centralizer subgroup functors and the published Iwasawa transport under
rational conjugation. Its compact subgroup is the conjugate compact,
including the original compact for representatives lying in it.

`translatedCoefficient` tensors the two actual left translations
`f(x) ↦ f(g⁻¹ x)` using
`CoefficientConjugation.leviCoefficientLeftTranslation`. The conjugation of
the induced dual uses the published same-functional identification of the
smooth contragredient. The product map then applies the exact inducing
transport `ActualConjugateLeviTensor.coefficientCongr` from the conjugate
of the twist to the twist of the conjugate. Here the parameter transport
is `conjugateParameter` on the full rational-character parameter torus.
The construction uses the same positive-Levi normalization on both sides.
The compact data provide the compactness of both parabolic quotients.

`genericLocus` is the inverse image of the actual simultaneous regular and
invertible locus for the target-side continued standard pair and its
reverse dual pair. `genericComparison` applies their published common-Levi
tensor after `translatedCoefficient`. This gives exactly the composition
of the forward standard continuation and the inverse of the reverse
standard continuation on the induced dual with the two actual left
translations, in the canonical product coefficient model. Its type retains
equivariance for the full external product of the rational-point actions.

This algebraic construction makes continuation data explicit. Existence
of those data, full unitary regularity, and V.3.2 are separate propositions.
