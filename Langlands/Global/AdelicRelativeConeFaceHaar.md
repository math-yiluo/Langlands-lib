# Relative split Haar in the face coordinates

`RelativeConeFaceHaarStatement` fixes nested standard parabolics with indices
`I ≤ Q`, a minimal Iwasawa compact, and an enumeration of the simple roots
outside `I`. For every Haar measure on the actual relative positive split
subgroup of `Q`, it provides a complementary coroot coordinate map and a
positive measure factor. The coroot coordinates reconstruct the ambient
minimal height of each split point. The same factor works for every pair of
cutoffs. On the actual strict characteristic shell the pushforward is the
factor times Lebesgue measure restricted to `relativeConeFaceStrictBase`.

The proof begins with `relativeCorootHaar`. Its logarithm on the maximal
split torus gives the minimal Iwasawa height by
`minimalHeight_eq_of_torusLog`. The outside roots of `Q` are in bijection
with the complementary indices of the face. Reindexing the logarithm along
this bijection preserves the product Lebesgue measure. The actual strict
shell is the inverse image of the corresponding coordinate set, which is
measurable by the inverse coordinate map and measurability of the actual
shell. Restricting the pushforward identity gives the claim.

This transports the split Haar factor of (7.23) to the coordinates of the
split-variable identity (7.26). The factor is for one split chart. A comparison
across successive Levi restrictions also involves the Haar measures on the
radical quotients, the Levi quotients and the compact groups.

Source. P. Delorme, *On the spectral theorem of Langlands*, Advances in
Mathematics 426 (2023), 109107, §7, journal pp. 28–30, (7.23) and (7.26).
