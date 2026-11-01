# Exactness reflection by actual Jacquet detection

This internal module connects the published exact normalized Jacquet maps
with actual subquotient detection. It does not assume an abstract faithful
functor. Its detecting condition explicitly refers to nonzero actual smooth
subquotients and their actual unipotent coinvariant carriers.

`DetectsSubquotients F T P A` means that every nonzero actual smooth
subquotient of `A` has a nonzero Jacquet module for some block shape satisfying
`P`. Actual subquotient transitivity passes this property to a subquotient.
`detects_cuspidalInduction` proves a concrete instance: induction of any actual
quasicuspidal Levi representation is detected by the family of Levis associated
with the inducing Levi. This uses the published
`cuspidalInductionSubquotientJacquet`, which applies minimal nonzero
quasicuspidal Jacquet descent and the nonassociated Jacquet subquotient
vanishing theorem. Neither irreducibility nor finite length is needed for this
detector.

`injective_of_jacquet` applies detection to the actual kernel. The kernel
inclusion stays injective under normalized Jacquet descent because its ambient
representation is smooth. Its composition with the given map is zero.
Injectivity of the given maps in the detecting family therefore makes every
detected Jacquet module of the kernel zero. Detection makes the kernel itself
zero and proves injectivity.

For `exact_of_jacquet`, the composite of two actual smooth maps is required to
be zero. The outgoing map descends through the actual quotient of the middle
term by the incoming range; this map is `cokernelDesc`. The coinvariant
quotient maps are right exact, so their kernel on this quotient projection is
the incoming Jacquet range. Exactness in the chosen Jacquet family makes every
descended outgoing Jacquet map injective. The quotient inherits detection
from the middle term, and the injectivity reflection just proved applies.
Injectivity of the descended outgoing map gives equality of the original
incoming range and outgoing kernel. No sequence is asserted exact at a
surviving terminal quotient.

The construction uses actual invariant submodules and their actual module
quotients with the published smoothness transfer, normalized action and
normalization of morphisms. The statement is valid at every natural rank and
for arbitrary field and representation universes. It does not prove that the
degrees or homology of the Aubert cut complex lie in the inducing
cuspidal-support class. A concrete detector for those actual degrees is still
needed before the associated-Levi specialization proves their concentration.
The contribution supplies no signed-effectivity or irreducible-image theorem.
