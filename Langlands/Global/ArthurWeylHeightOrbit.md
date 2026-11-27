# The transported line character on a Weyl orbit

For a line preserved by the minimal standard parabolic, choose coordinates diagonalizing the generic cocharacter and retaining the original coordinate eigenvector. The rational Weyl lift sends that eigenvector to a vector supported in one cocharacter weight, as follows by conjugating the cocharacter by the lift. Choose a nonzero coordinate of that vector.

The normalizer preserves the standard minimal Levi, the centralizer of the maximal split torus. Conjugating by the inverse lift on the Levi and using the Levi retraction of the minimal parabolic gives a transported line character. Its torus restriction is the Weyl translate of the original. With the minimal parabolic written in radical-times-Levi order, the Levi acts on the transported vector by that character. The unipotent block matrix is the identity on the selected degree, so the selected coordinate records the character times its original nonzero scalar.

For `y = w v x` with `v` in the minimal adelic radical, applying the inverse matrix of `y` to the transported vector gives the result of applying the inverse matrix of `x` to the original vector. The radical fixes the original vector because its line character is trivial there. The eigenline comparison of primitive heights then proves the uniform additive logarithmic inequality of `exists_weylLineHeight_bound`.
