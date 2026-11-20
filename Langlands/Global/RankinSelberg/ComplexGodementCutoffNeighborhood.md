# Invariant rectangular neighborhoods for Godement tests

Given an open neighborhood of the smaller unitary group inside the smaller general linear group, the proposition gives an open right-unitary invariant neighborhood of the unitary trailing rows in the rectangular matrix space. If the trailing rows of `diag(1,h)` lie in the rectangular neighborhood, then `h` lies in the given smaller neighborhood.

Lean first takes the closed set of rectangular matrices whose first column vanishes and whose trailing square block is outside the image of the given open set. Its right-unitary saturation is closed. Indeed right multiplication is the composite of a homeomorphism of the product with the unitary group and the projection with compact fibers. The complement is invariant. A unitary trailing row matrix in that closed set would have a unitary trailing square block, as follows by computing its row Gram matrix. Thus the complement contains every unitary trailing row matrix. Applying the closed condition to the trailing rows of `diag(1,h)` proves the required implication.

This is an internal compact cutoff step for Jacquet's Godement spanning assertion, in the upper Borel convention.

Source: Hervé Jacquet, *Archimedean Rankin–Selberg Integrals* (2009), §7.1, Proposition 7.1(v), pp. 44–46.
