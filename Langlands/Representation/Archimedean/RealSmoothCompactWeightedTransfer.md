# Transfer of compactly weighted real group translates

`RealSmoothCompactWeightedTransferStatement` concerns an admissible real Harish-Chandra module \(V\) with two compact and Lie equivariant maps \(e\) and \(f\) into genuine smooth Banach carriers. Assume \(e\) is injective and both Banach actions are jointly continuous. Let \(\phi\) be a continuous scalar function on the orthogonal subgroup in a supplied finite-dimensional left-translation type. For \(g\in GL_n(\mathbb R)\) and \(v\in V\), there is a single \(z\in V\) whose underlying \(e\)- and \(f\)-values are the two Haar averages of \(R_i(kg)v_i\) weighted by \(\phi(k)\), where \(v_1\) and \(v_2\) are the corresponding values at \(v\). The three carrier universes are independent.

`realSmoothCompactWeightedTransfer` pairs the two maps into the smooth vectors for the diagonal action. The chain rule for the bounded coordinate projections shows that this pairing respects differentiation. The closure of the underlying paired image is group invariant by `realSmoothGKImageClosure`. The weighted average of the diagonal orbit at \(g\) belongs to that closed subspace, since the norm quotient map annihilates the integrand and commutes with the Bochner integral.

The algebraic paired image is a quotient of the admissible compact action on \(V\) under the identification of the matrix orthogonal group with the orthogonal subgroup of the units. The finite translation type of the weight makes the average compact-finite by `isFiniteVector_compactWeightedOrbit`. Applying `admissibleCompactFiniteClosure` puts the average in the algebraic image, and the two coordinate projections give the asserted identities.

The result gives a transfer of compact orbit reconstruction identities for the principal-series estimate in Bernstein–Krötz, *Smooth Fréchet globalizations of Harish-Chandra modules*, §8 and Appendix A.

`realSmoothCompactWeightedTransfer_orthogonal` gives the formula on orthogonal
matrices with a left-invariant Borel probability measure. It transports the
measure, translation type, and continuous coefficients along the multiplicative
homeomorphism `orthogonalCompactEquiv` and applies the same graph integral.
