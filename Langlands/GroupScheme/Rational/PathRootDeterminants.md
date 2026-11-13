# Determinants of the two endpoint root groups

This internal prerequisite extends the normalized path matrix infrastructure. Its data are an arbitrary field `k : Type u`, an actual affine group scheme with a supplied split pinning, a highest-weight representation fundamental at the first vertex of a supplied path component, a normalized simple-root family and a nonzero initial vector. No parity assumption is used.

`normalizedPathDetOne` is the subgroup of rational points whose matrix in the normalized path basis has determinant one. Multiplicativity of the matrix map and determinant proves closure, including under inverses.

`exists_normalizedPathMatrix_transvection_of_isRepresentedBy` treats any additive map representing a supplied subgroup functor and equivariant for a difference `epsilon_i - epsilon_l` of distinct path weights, in either direction. Higher divided powers vanish. The first divided power maps line `l` into the one-dimensional line `i` and kills every other path line. The published expansion of rational points as `1 + c A_1` therefore gives a transvection matrix `1 + single i l a` in normalized coordinates, for some scalar `a` in the original field.

`normalizedPathMatrix_det_eq_one_of_mem_rootSup` applies this to linked parametrizations of the positive and negative root subgroups for any supplied positive path root. Both have transvection matrices with determinant one. Their subgroup supremum is contained in `normalizedPathDetOne`, giving determinant one for every rational point it generates.

The provenance is the published divided-power path support results, one-dimensional path weight spaces, rational additive-point expansion and Mathlib's transvection determinant theorem. This unit makes no direct literature claim. It is infrastructure for the supplied merged reflection representative; its matrix and the cross-section theorem remain further work.
