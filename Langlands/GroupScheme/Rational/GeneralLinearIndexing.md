# Adjacent characters and block subsets of the diagonal torus

This internal adapter constructs actual characters and cocharacters of the
published diagonal torus in `GL_N` over every field `k`. It uses the published
integer coordinate equivalences; it introduces no root-system assumptions.

`adjacentRootPair a` is the pair of coordinates `(a,a+1)` for
`a : Fin (N-1)`. `simpleRootCharacter k a` is the actual character with
coordinate vector `e_a-e_(a+1)`. The coordinate and pairing lemmas identify
its pairing with a cocharacter as the difference of its adjacent weights.
The character map is injective, by the published injectivity of nonzero
ordered root vectors. This file does not assert that these characters are
exactly the simple relative roots; that is a separate statement and proof.

`cocharacterOfWeights k w` is the actual torus cocharacter with integer
weights `w`. Its composite with the diagonal inclusion is the published
`diagonalCocharacter`, as proved using the existing split-torus point formula.

`blockSimpleRoots k B` is the image of `B.uncuts` under the adjacent-character
map. The published cuts of an ordered positive block shape are its interior
boundaries; their complement comprises the edges inside the blocks. The
membership and injectivity lemmas therefore identify the root subset with
those edges and recover the block shape from the subset.
`existsUnique_blockSimpleRoots` proves that every subset of the adjacent
characters is obtained from exactly one block shape: take its inverse
image in `Fin (N-1)`, complement it to get the cuts, and apply the published
cut equivalence. Injectivity gives uniqueness. The definitions also apply
to `N=0` and `N=1`, when there are no adjacent edges.

These are derived finite-coordinate adapters for the standard-block
description in Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second
edition (2015), Example 2.1.1, printed pp.45–47, and Renard,
*Représentations des groupes réductifs p-adiques*, 2026 version, V.3.8,
printed p.111. Neither source uses the Lean cut-set encoding or the
choice-free standard-subgroup intersections. The adapters prepare that
comparison; they do not prove the general Borel–Tits structure theorems
or the GL standard-subgroup comparison.
