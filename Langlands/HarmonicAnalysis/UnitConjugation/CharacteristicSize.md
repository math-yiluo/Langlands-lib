# A homogeneous size from characteristic coefficients

For a finite-dimensional normed algebra `A` over a nontrivially normed field `F`, `characteristicSize F x` is the maximum of `‖cᵢ(x)‖ ^ (1 / (d − i))` over the coefficients below the leading term of the characteristic polynomial of left multiplication by `x`, where `d` is the dimension of `A`. The maximum over an empty index set is zero.

The size is invariant under unit conjugation, is multiplied by `‖a‖` under scaling by `a : F`, and vanishes exactly on the nilpotent cone. The coefficient scaling identity follows by factoring `a` out of the characteristic determinant when `a` is nonzero. A size at most one bounds every characteristic coefficient by one.

`CharacteristicSizeStatement` gives continuity over a complete ground field and local constancy wherever the size is positive when the field is ultrametric. Continuity follows from the polynomial coefficient maps and the finitely many positive roots. Near a point of positive size, the norms of its nonzero coefficients are locally constant by the ultrametric inequality. The other weighted norms remain below the size of that point by continuity. Thus the maximum is locally constant there.

This is the characteristic-polynomial version for an associative algebra of the homogeneous invariant function used in the extension of Howe's theorem. [Harish-Chandra, *Admissible invariant distributions on reductive p-adic groups*, §11.2, Lemma 11.5 and its proof, pp. 60–61](https://doi.org/10.1090/ulect/016)
