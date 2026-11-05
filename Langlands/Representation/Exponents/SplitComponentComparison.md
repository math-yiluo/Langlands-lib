# Exponent comparisons for central actions

Author: Worker 1666. Internal supporting derivations for Renard 2026, VII.1.1.

Restriction along a group homomorphism retains the same uniform nilpotence
exponent. If the original weight spaces span, any nonzero restricted character
must equal the restriction of an original nonzero weight. Otherwise all
original spaces lie in the sum of the other restricted weights; independence
would force the proposed weight space to be zero.

A linear map commuting with the specified central actions preserves each
uniform character space. If it is onto and the source weights span, target
independence similarly reflects every nonzero target weight to a nonzero source
weight. The target representation need only be smooth.

`GeneralizedWeightReflectionStatement` names this containment of the target's
nonzero central weights in the source's nonzero central weights.
`generalizedWeightSpace_ne_bot_of_surjective` proves it from smoothness, source
spanning and a surjective linear map intertwining the two central actions.
The ambient groups and their carriers have independent universes; they need
not agree. Both have the nonarchimedean and local compactness hypotheses of the
published characteristic-space construction.

`exists_generalizedWeight_comp` assumes an admissible source over an
algebraically closed field and a continuous original central map. These
hypotheses supply its source spanning. It does not require the homomorphism
of acting groups used for restriction to be continuous. Smoothness of the
resulting character can be established separately by the published open-kernel
criterion when the original map is continuous.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, VII.1.1, printed pages 220–221 / PDF pages
226–227, registered as `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
These are internal algebraic derivations motivated by its two exponent
comparisons. They use `SplitComponentDecomposition` and
`SplitComponentWeights`; they do not themselves identify the normalized
induction or Jacquet maps with a central intertwiner.
