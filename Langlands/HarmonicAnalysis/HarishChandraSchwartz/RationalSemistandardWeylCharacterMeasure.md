# Conjugation of the source character Haar measure

Waldspurger (2003), I.1, printed p. 239, normalizes unitary unramified
character Haar by restriction to the split component. In the Library,
`unitaryCharacterHaar_univ` gives its total mass as the cardinality of
the actual unitary restriction kernel.

Under actual Levi conjugation, a literal character is trivial on the
source split-center image exactly when its conjugate is trivial on the
target image. The canonical model character homeomorphisms identify
these subgroups with the kernels of the two scheme restriction maps.
`restrictionKernelConjugation` assembles the resulting multiplicative
equivalence of the kernels.
`restrictionKernel_card_conjugate` proves equality of their cardinalities.
The Haar uniqueness theorem for compact groups gives
`unitaryCharacterHaar_map_conjugation` at the resulting common mass.
The two source split-valuation-image finite-index inputs are the ones
used to construct the measures on the respective Levis.
