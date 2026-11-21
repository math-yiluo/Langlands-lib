# Naturality of the finite dual evaluation pairing

For an actual Hopf-algebra map, `pointCharacter_dualMap` compares the two evaluations obtained by applying the original map to a point or its dual map to a character. The associated coefficient tensors are related by applying the Hopf-algebra map in the first tensor factor. The proof checks that relation against every dual functional. Evaluating the two tensors at a point then gives the same unit on both sides.

`finiteSchemePairing` transports this evaluation from the actual affine Hopf coordinates of a finite locally free commutative group scheme to the group scheme itself. It is multiplicative in both points and commutes with restriction to any test scheme. `finiteSchemePairing_dualMap` proves adjointness of an actual group scheme map and the constructed map of its finite dual spectra. These identities apply to the maps in the scalar torsion diagrams.

The module derives these identities from the dual algebra and evaluation of Demazure and Gabriel (1970), Chapter II, §1, no. 2, 2.10, printed pp. 156–158 (PDF pp. 186–188). They supply the evaluation pairing for the Cartier dual factor used by Rapoport–Zink (1996), §6.43, printed p. 309 (PDF p. 321).
