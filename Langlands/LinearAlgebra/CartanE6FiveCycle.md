# A permutation basis for a five-cycle in the E₆ Weyl group

`TypeE6FiveCycleStatement` applies to an integral based root datum whose Cartan matrix is `CartanMatrix.E 6` and whose coroots generate its cocharacter lattice. The element `fiveCycleWeyl` is a product of the reflections at vertices `4`, `3`, `2`, `0`, in that order for the root-datum automorphism group. It has order five. On an integral cocharacter basis the coweight action cycles the first five vectors and fixes the last.

The first five vectors are the consecutive suffix sums of simple coroots along the path with vertices `0, 2, 3, 4, 5`. The last is the simple coroot at `1` minus the simple coroot at `4` and twice the simple coroot at `5`. The basis matrix and its integral inverse are checked by multiplication. The Cartan formula for the simple coreflections gives the stated action on the six columns. Faithfulness on the cocharacter lattice implies that the fifth power is the identity, and the action on the first column gives nontriviality.

The permutation basis gives an integral calculation relevant to the Sylow-five step of Platonov and Rapinchuk, *Algebraic Groups and Number Theory* (1994), §6.8, Proposition 6.21, printed pp. 375–377. It uses the four consecutive vertices of an A₄ path in the E₆ Cartan diagram, given as (6.52) on printed p. 379.
