# Fixed points of scalar-extended torus units

This is an internal interface for the unramified building covering argument.
`IsFixedByScalarTorusUnits` says that every rational point of the extended
source group in its character-valuation kernel fixes a supplied point, through
the extended group morphism. For a split torus, the character-valuation kernel
is its unit subgroup. The definition also permits arbitrary source group
schemes so that group-scheme conjugacy witnesses can be used directly.
`IsFixedByUnramifiedTorusUnits` specializes to the maximal unramified extension
and its canonical valuation.

The conjugacy lemma is elementary and does not assume building descent.
Base change carries the supplied conjugacy equation to the inner automorphism
of the extended rational point. Functoriality of the character-valuation kernel
carries each unit to a unit in the other source. Applying the inverse
conjugator to the fixation equation gives the result.

Coefficient extension is fixed by the Galois action by the imported theorem
`Langlands.GroupScheme.GaloisPointComparison.rationalConjugate_rationalExtend`
from `RootBuildingGaloisFieldExtension`. Its proof compares coefficient conjugation
through the coefficient-point equivalence. No duplicate fixation lemma is declared
here. These are derived internal constructions and proofs, not additional geometric
assertions from the literature.
