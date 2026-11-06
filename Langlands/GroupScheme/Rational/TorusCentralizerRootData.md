# Actual root data on the retained finite-Galois centralizer model

Author: Worker 1293.

This internal adapter retains a supplied `TorusCentralizerFiniteGaloisModel C`
over an arbitrary field and universe `u`. It does not choose another torus or
another splitting field.

`TorusCentralizerRootData C` stores two finite reduced Mathlib root data on the
actual character and cocharacter lattices of the retained torus over the
retained field. The ambient datum belongs to the actual composite of the torus
map through the supplied centralizer inclusion. The second datum belongs to
the actual torus map into the centralizer. Both assertions use `IsRootDatumOf`,
including the actual lattice pairing, actual roots, and normalizing-point
realizations of reflections. The root indices remain in universe `u`.
The two original groups are assumed affine for these predicates.

`TorusCentralizerFiniteGaloisModel.rootData` constructs these data from explicit
proofs of connected reductivity for the two original groups and the supplied
proposition `RootDatumExistenceStatement`. It applies the proved preservation
of connected reductivity over the retained field, then applies that supplied
existence proposition to each stored split maximal-torus map. Thus root-datum
existence is an input to this construction, not a result proved by this module.
The supplied finite-Galois model already contains both maximality assertions.

`separatingCocharacter` is precisely the canonical base change of the rational
model's original-field separating cocharacter. It requires that the original
subtorus be split and that the ambient group be locally of finite type.
`separatingCocharacter_galois` specializes the rational model's fixedness lemma:
every ordinary Galois automorphism of the retained extension fixes this same
cocharacter.

When the centralizer is also locally of finite type and its supplied inclusion
represents the original torus centralizer, `centralizer_root_range` identifies
the range of the actual centralizer roots with the actual ambient roots pairing
to zero against this cocharacter. Its proof specializes the rational model's
arbitrary-field root comparison, rewrites its ambient map as the actual
composite, and uses the two `IsRootDatumOf` root and pairing identities.
`ambient_root_mem_centralizer_iff` expresses this equality on ambient root
indices using `RootPairing.root'`. It makes no assertion identifying coroots
of the two separately indexed data.

The provenance is an internal composition of the supplied root-datum existence
proposition and the imported finite-Galois, reductive base-change, rational
cocharacter and root comparisons. No new literature theorem is asserted.
This pair does not discharge root-datum existence, the maximality-ascent input
used to obtain a finite-Galois model, derived-group geometry, the actual
cocenter character-image comparison, or based-root descent. These remain
separate obligations of the unconditional Levi cocenter root-model proof.
