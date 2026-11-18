# Column factorization for Whittaker descent

An upper-unipotent matrix fixing the first `p` columns of the identity factors as a column matrix supported above the `p`-th diagonal position, followed by an upper-unipotent matrix fixing the first `p + 1` columns. Indices start at zero. The proof clears column `p` by multiplying by the negative column vector. It uses the Library's mirabolic radical in rank `p + 1`, embedded by adjoining an identity block.

The next stage fixes the span of the first `p + 1` coordinate vectors pointwise. It is preserved by conjugation by the column group and by the Levi in the first `p` rows and columns. The latter also preserves the trailing block and acts on the column vectors by ordinary matrix multiplication. These internal matrix facts support the finite-field construction of Whittaker vectors.
