# Positive rational quotients under the adelic Weil comparison

The module compares the full adelic group, its principal and norm-one points, and its positive rational quotient under Weil restriction. An isomorphism from the lower group to the Weil restriction is allowed in all the comparisons.

For positive torus data with injective, finite-index character restriction on both fields, inclusion of the lower positive image in the upper one gives equality. Indeed, lift an upper positive point to the lower adelic group and factor the lift into its positive and norm-one parts. The upper-field factorization sends the images of these parts to the original positive point and the identity, respectively. The forward inclusion holds for a central split torus below and a split component above by `map_imageSubgroup_le`. The resulting quotient homeomorphism respects right translation.

The Haar pushforward on the norm-one groups is a positive finite scalar multiple of the upper Haar measure by uniqueness. The same scalar compares the discrete norm-one quotient measures by `LeftCosetSpace.measurePreserving_discreteQuotientMeasure`. The positive rational quotient measures have been defined by pushforward from the norm-one quotients, so they carry the same factor. Right invariance of norm-one Haar also transfers through this positive rescaling.

The comparison uses the Library's `normOneComparison`, following Springer, *Reduction theory over global fields*, §1.4, pp. 208–209, and §3.1(a)–(b), p. 214, `springer-1994-reduction-global-fields`, SHA-256 `774f5531200db07140b30ffb8f4adce8cf3a3914ca9f38b796f2a2d24ff18496`.
