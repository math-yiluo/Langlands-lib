# Actual source density models for archimedean multiplicities

This internal construction for the cuspidal contragredient of dual cusp forms
(`CuspidalTransposeInverseContragredientStatement`) connects the published existence of
actual irreducible admissible place components to the implemented finite-family
pairing assembly. Its sources are the Library's proved component-existence,
restriction, finite-factor evaluation, contraction, and finite-family results.

`PlaceDensityModels` records one actual irreducible admissible subspace at
each real or complex infinite place. The compact and complexified local Lie
actions restrict to these subspaces. The published genuine real and complex
GK restriction results give local finiteness and weak continuity. Together
with irreducibility and admissibility, these supply every hypothesis of
simultaneous GK density. Every cuspidal realization admits this data by the
published real and complex place-component existence theorems.

The inclusion of each local source into the realization is a nonzero
simultaneous compact and Lie intertwiner. Under the actual finite-factor
tensor evaluation equivalence, both place actions operate on the second
factor. Some linear functional on the first factor contracts this
inclusion to a nonzero intertwiner into the archimedean multiplicity
space. This proves that every chosen source occurs in that multiplicity
space; it does not assume an irreducibility assertion for an individual
place action on the whole multiplicity space.

Finally `multiplicityPairing` applies the proved finite-family assembly
to these source embeddings and the commuting jointly irreducible family
of actual multiplicity actions. Given nonzero local pairings for supplied
compact and Lie twists, it constructs a nonzero pairing on the actual
multiplicity space satisfying all local twist identities simultaneously.
The twists remain parameters here. No local pairing existence theorem or
unconditional global contragredient theorem is asserted by this module.
