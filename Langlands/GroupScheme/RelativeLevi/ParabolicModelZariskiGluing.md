# Zariski gluing of smooth proper parabolic models

For a fixed reductive group scheme over an arbitrary scheme, this internal
construction assembles supplied smooth proper parabolic models on an
arbitrary open cover of the base into an actual smooth proper model over
the entire base. The cover is indexed in the base universe. There is no
finiteness, affineness or quasi-compactness hypothesis.

`SmoothProperModel.nonempty_of_openCover` takes an actual model of the
pulled-back group on each open chart. The canonical direct/iterated
pullback comparison identifies each local model's represented presheaf
with the restriction of the original parabolic presheaf. The lifted
Yoneda equivalence converts these representing bijections to local
natural isomorphisms on the full slice.

The actual parabolic presheaf is a big Zariski sheaf. The imported
`LocalRepresentation.exists_representation_zariski` therefore glues these
local representations to a scheme over the original base and a natural
representing isomorphism. Smoothness and properness are Zariski local on
the target; `property_of_local_representations` transfers both properties
from the same supplied local models to this same global structure map.
Converting the global natural isomorphism back to representing bijections
gives the claimed `SmoothProperModel`.

`SmoothProperModel.zariskiGlue` chooses the global model from this proved
nonemptiness. Its universal relative-parabolic family is available through
the imported `SmoothProperModel.universalFamily`.

This is an internal composition of the imported actual presheaf,
base-change comparison, scheme gluing and local morphism-property results.
It assumes the local models and does not prove their existence, finite
parabolic types, or effective scheme descent along an etale cover. No new
literature translation is claimed.
