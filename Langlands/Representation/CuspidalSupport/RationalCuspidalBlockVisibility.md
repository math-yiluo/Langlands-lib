# Compact visibility of actual cuspidal inertia blocks

This internal supporting unit relates the published proper-standard
cuspidality and actual rational inertia classes. The field universe `uF`
and representation-carrier universe `uV` remain independent. No
admissibility, finite length or finite-dimensionality hypothesis is used.

`isCuspidalFor_characterTwist_iff` applies the actual normalized Jacquet
character-twist equivalence to every member of a supplied test family.
It requires the smooth character to be trivial on each tested radical.
Normalization changes the action, while the equivalence preserves
vanishing of the actual quotient carrier.

`limitOfCompactSubgroups_le_rationalCommonNormKernel` proves that a
subgroup whose every compact subset is contained in a compact subgroup
lies in the actual common rational norm kernel. For a given element,
apply compact containment to its singleton. The image of the resulting
compact subgroup under the actual subgroup inclusion is compact, so the
published rational norm-kernel containment for compact subgroups applies.

`standardUnipotent_le_rationalCommonNormKernel` uses the published compact
containment theorem for the actual standard radicals. Its structural
inputs are a connected reductive group, a maximal split torus, a generic
cocharacter and `StandardCocharacterStatement`. It makes no assumption
about representation finiteness or a category decomposition.

`isCuspidal_rationalUnramifiedTwist_iff` now applies the first comparison to
the exact `IsCuspidal` predicate: every proper actual standard normalized
Jacquet module vanishes. An actual rational unramified character kills the
common norm kernel and therefore all these radicals.
`isCuspidal_iff_of_rationalInertiaRelated` combines this with invariance
under actual smooth isomorphisms.
`isCuspidal_of_rationalCuspidalInertiaClass_eq` takes a cuspidal
representative from the published class subtype and proves cuspidality
of every irreducible object in that class.

`RationalCuspidalInertiaClassBlock` names the full subcategory of the
existing `rationalCuspidalInertiaClassBlockProperty`. It permits arbitrary
objects whose irreducible actual subquotients all have the specified
class. It does not impose finite length or choose a representative.

`compactFiniteFixedVectorSupport_rationalCuspidalBlocks` assumes
compact-level finiteness of the actual irreducible cuspidal inertia
classes, with exactly the fixed-vector meaning used by the published
`RationalCuspidalInertiaFinitenessStatement`. It takes one arbitrary
object from each actual class block. A nonzero fixed vector survives
in an actual irreducible subquotient; block membership identifies its
class, and the preceding comparison makes it cuspidal. The visible block
support embeds into the supplied finite set of visible inertia classes.

Worker 1751 derives this unit from the published actual compact
containment, rational norm-kernel, normalized Jacquet twist, inertia
quotient and fixed-vector constituent APIs. It is an internal comparison,
not a new assertion attributed to literature. Compact-level inertia
finiteness remains an explicit premise, as do the structural standard
family inputs. No decomposition, generator stability or uniform
compression theorem is established here.
