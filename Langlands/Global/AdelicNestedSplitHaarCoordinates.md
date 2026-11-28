# Haar coordinates for nested relative split factors

`NestedSplitHaarCoordinatesStatement` concerns \(P_I\subseteq P_Q\).
The split coordinates for \(Q\) in \(G\) are indexed by the simple roots
outside \(Q\). The split coordinates for \(I\) in \(M_Q\) are indexed by the
roots inside \(Q\) and outside \(I\). The two underlying split vectors
belong to the same maximal split torus. Their sum gives the vector in the
relative split space for \(I\) in \(G\).

`nestedRelativeSplitAdd` takes the ambient weights of this sum. The
projected coroot for a root shared by \(M_Q\) and \(G\) agrees at the
intrinsic and ambient \(I\) levels. Consequently the inner split vector
has its original coordinates on the roots inside \(Q\) and has zero
coordinates on the roots outside \(Q\). The outer vector has its original
coordinates on the roots outside \(Q\). Its weights inside \(Q\) add a
translation of the inner coordinates for each fixed outer vector.
Reindexing product Lebesgue measure and applying the measure-preserving
translation on each inner fibre proves the exact pushforward.

`relativeSplitCoordinatesEquiv` uses the logarithm and projected coroot
basis from `relativeCorootHaar`. Each Haar measure on the actual relative
split subgroup is the pushforward of a positive multiple of coordinate
Lebesgue measure. The statement also identifies actual split points under
the sum. Their positive torus lifts have the three prescribed logarithms.
Since the torus logarithm is additive under multiplication and injective
on positive points, the ambient point for the sum is the product of the
two split points.

This compares the split coordinate factors of the successive Iwasawa
integrations in the face decomposition (7.26).

Source. P. Delorme, *On the spectral theorem of Langlands*, Advances in
Mathematics 426 (2023), 109107, §7, journal pp. 28–30, (7.23) and (7.26).
