# Retraction from an isolated irreducible central grade

Author: Worker 526. The namespace is
`Langlands.FilteredCentralRetraction`. This internal algebraic deduction
combines the published `IsolatedCentralCharacter` construction with
`groupedCentralCharacterRetraction`. The group, ambient carrier and source
carrier have independent universes.

`scalar_character_unique` proves that an exactly scalar central action has
only its specified generalized character: a central element distinguishing
two character values would force the given nonzero generalized vector to
vanish. `character_unique_of_filtration` applies finite-filtration
occurrence detection. If all grades except one exclude every character
satisfying a predicate `P`, any ambient `P`-character equals the scalar
character of that grade.

`grouped_singleton` identifies the grouped space for equality with one
character with its actual generalized central-character space, by the two
supremum inclusions.

`retractionOfIsolatedGrade` assumes finite full-central operator span, the
stated filtration exclusion, an irreducible scalar distinguished grade,
and a nonzero injective scalar-central map from the source. The published
isolated-block construction identifies the entire generalized block with
that source. The published grouped retraction, specialized to a singleton
predicate, projects the whole ambient representation onto this block.
Composing with the inverse block equivalence gives an actual equivariant
map back to the source.

The resulting maps compose to the identity on the source. They also fix
every generalized vector whose character satisfies `P`: the zero vector
is immediate, and a nonzero vector makes that character occur, so the
preceding uniqueness theorem identifies it with the selected character.
One pair of maps works for all qualifying characters. Uniform generalized
nilpotence is retained; no semisimplicity or representation-carrier
dimension hypothesis is introduced.
