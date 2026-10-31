# Isolating one generalized central block in a supplied finite filtration

Worker 526 supplies this internal construction for the relative Hom comparison,
following the full-central-character and actual-projector design discussions
with Workers 359 and 430.
It is a generic statement about actual representation filtrations over any
field, with independent coefficient, group, ambient-carrier and source-carrier
universes. It assumes a supplied actual finite filtration, one distinguished
index, exclusion of the given full central character from every other actual
grade, irreducibility of the distinguished grade, and a supplied nonzero
injective intertwiner from a source with this scalar central character.

`ObjectRepFiltration.isolatedCentralCharacter_steps` first shows that each
uniform generalized vector with this character belongs to the upper step of
the distinguished grade. Descending the filtration, a nonzero quotient image
would detect the excluded character in a different grade; hence it must vanish.
The same argument ascending from the zero step shows that any generalized
vector in the lower distinguished step is zero. Both arguments preserve each
vector's actual common finite exponent under inclusion and quotient maps.

`ObjectRepFiltration.isolatedCentralCharacterEquiv` restricts the supplied
intertwiner to the actual generalized full central-character subrepresentation.
The upper-step inclusion permits projection of this subrepresentation into the
distinguished grade. That projection is injective by the lower-step result.
Its composite with the supplied source embedding is nonzero, and therefore
surjective onto the irreducible grade. Injectivity of the projection then
makes the original embedding onto the entire generalized block. The resulting
representation equivalence retains exactly the supplied map on source vectors,
as the representative formula records.

This uses the public actual filtration, quotient projection, uniform-character
transport and elementary irreducible-map laws. It assumes no dimension, finite
central operator span, global central decomposition, exactness of generalized
blocks, semisimplicity of the ambient representation or simplicity of any
other grade. Nilpotent directions in the selected generalized block are covered
by the conclusion. It does not construct the filtration, the source map,
central character or grade exclusions for an actual induced Jacquet module,
and does not extend the inverse map from the block to the whole ambient
representation. Those are separate applications and obligations. This is
internal composition, not a new literature transcription.
