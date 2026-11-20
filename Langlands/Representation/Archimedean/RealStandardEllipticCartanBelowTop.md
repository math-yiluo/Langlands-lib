# Vanishing below the elliptic rank of a regular real Cartan

`length_slots_eq_count_induced` counts the rotation slots of an original block list. Induction on the list skips one position for a real character and two for an induced block. The first position of each induced block contributes one slot. The rank condition ensures every such slot fits in the matrix. A permutation of the block list preserves this count.

`realStandardEllipticCartanBelowTop` applies the compact Fourier support theorem to the separated regular Cartan matrix. The lower-coordinate tests concentrate at the identity, so eventually the compact trace is the signed low-mode trace. It vanishes eventually when the original list has fewer rotation slots than the source Cartan. `tendsto_compactTestTrace_of_lt` states the corresponding limit on the filter of normalized continuous compact tests.

This is an internal consequence of the regular Cartan matrix realization, the compact trace support calculation and the normalized peak tests.
