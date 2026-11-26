# Inducing characters of the Borel Levi

The determinant on each `GL₁` block gives `singletonCoordinates`. Its inverse
places the given units on the diagonal. `borelCharacter F z` multiplies the
unramified block characters. It is trivial on the integral diagonal and
takes the value `z i` at the `i`th uniformizer element. The tensor of the
block characters acts by this scalar on the whole inducing line, as follows
by evaluating the tensor action on pure tensors.

Each block has only one coordinate, so every permutation is minimal and
normalizes the diagonal Levi. A standard refinement of a size-one block has
length one, so there are no proper standard Levi refinements. Inverse
conjugation by a permutation matrix acts by precomposition on the diagonal
entries. Reindexing the product in `borelCharacter` shows that geometric
transport by `w` corresponds to the tuple `z ∘ w.symm`.

These identities specialize the Weyl transport used in the geometric lemma
to the normalized principal series in Henniart–Lemaire, I.5.4.
