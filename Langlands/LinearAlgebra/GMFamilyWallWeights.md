# Chamber weights across a wall

`adjacentAlong_unique` uses the signs of the restricted roots to characterize the chamber across a specified wall. Roots off the normal line keep their signs, and roots on it have their signs determined by the negative wall root. Adjacency reverses along that negative root and changes the chamber.

`volume_and_product_erase_of_adjacentAlong` uses the matching of simple roots modulo the normal line established in `GMFamilyRootWalls`. After reindexing by this matching, the new chamber vectors are obtained by negating the wall vector and adding multiples of it to the other vectors. The change-of-basis matrix is the identity with the wall column replaced, and its determinant is `-1`. The Gram matrix transforms by multiplying by the change-of-basis matrix on the left and by its transpose on the right. Its determinant and the Gram volume are preserved.

On the dual wall `Λ(v) = 0`, the matching roots off the line have equal evaluations. The two products with their respective normal factors removed therefore agree. This computes the denominator comparison needed in Arthur's residue cancellation using the weights `theta` from `GMFamilies`. It is an internal consequence of the chamber geometry and the definition of `gramVolume`.
