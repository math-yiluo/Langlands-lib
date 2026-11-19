# Complex coordinates for real compact standard modules

This internal construction provides matrix coordinates for the orthogonal action used in
the compact coefficient proof. The inducing positions are those of `realInducedBlockAt`.
Its two-dimensional blocks occupy successive positions, and `placement` identifies their
two axes and all remaining single axes with the original positions.

The basis change sends a pair of coordinates \(x,y\) to \(x+iy,x-iy\). Its inverse takes
the half-sum and the difference divided by \(2i\). The proof verifies the inverse by
multiplying the two matrices on each block. It conjugates the complexified orthogonal
matrix by this basis change to obtain `compactMatrix`. Continuity follows from the
continuity of the original entries and of finite matrix multiplication.

A real block rotation acts diagonally on the two complex rows with modes \(1\) and
\(-1\). A sign diagonal gives the sign of the first axis on both rows of a pair and
interchanges them when the original signs differ. A remaining row retains its sign.
The proof transports these formulas through the basis change using the real rotation
entry formulas and diagonal multiplication. It also reindexes the inducing character's
product through `placement`. The first axis of a pair contributes the sign raised to
the absolute weight plus one. The other axis contributes one, and each remaining axis
contributes its sign raised to its parity. The `signParameters` construction realizes
the common signs and pair interchanges with independent choices of actual diagonal
units.
