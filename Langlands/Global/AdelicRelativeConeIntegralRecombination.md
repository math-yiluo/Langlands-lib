# Relative coroot integration for the cone partition

`RelativeConeIntegralRecombinationStatement` fixes a standard parabolic
\(P_1\), with simple-root index `I`, and a finite coordinate enumeration of the
simple roots outside `I`. For `I ≤ Q`, the negative face has coordinates in
`Q` outside `I`. Its complementary split base has the coordinates outside
`Q`. The result recombines the regularized face integrals for a fixed
polynomial and spectral vector with nonzero coroot coordinates into the
regularized integral at the upper cutoff. The cutoffs \(T,S\) lie in the
ambient coroot span, and \(S\) is weakly dominant. The base integrals use
product Lebesgue measure in the complementary coordinates, restricted to the
strict split shell.

A point \(Y\) of the complementary split base is reconstructed by
`relativeSplitVector`. The placement of the base in the starting coroot
coordinates adds \(T_{P_1}-T_Q\). The outside weights of the two projections
of \(T\) agree on all roots outside \(Q\), so the placement preserves the
complementary coordinates. With the origin translated by \(T_{P_1}\),
`relativeTruncationConePartition` gives the decomposition into the split
member and a negative Levi face. `faceCell_iff` translates its support and
strict positivity requirements into the coordinate inequalities for the cell.
The inverse-Cartan weight comparison also shows that every cell is contained
in the upper-cutoff orthant. Uniqueness of the geometric decomposition gives
disjointness in these coordinates.

`regularizedOrthantPartitionIntegral` now gives the integral identity with
compact nonstrict bases. The coordinate reindexing preserves product Lebesgue
measure, so `relativeSplitBaseChart` identifies the restricted measures of the
nonstrict and strict bases. Rewriting by this equality gives the stated
strict-shell formula. This calculation concerns the split-variable integrals
of (7.26). The automorphic Levi pairings and the scalar comparisons between
the adelic quotient Haar measures enter when expressing them in these
coordinates.

Source. P. Delorme, *On the spectral theorem of Langlands*, Advances in
Mathematics 426 (2023), 109107, §7, journal pp. 24–25 and 28–30, especially
(7.8) and (7.26).
