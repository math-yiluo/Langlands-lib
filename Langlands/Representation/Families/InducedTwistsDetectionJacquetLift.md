# Lifting fixed vectors from an actual normalized Jacquet module

Author: Worker 70. Module
`Langlands.Representation.Families.InducedTwistsDetectionJacquetLift`, namespace
`Langlands.Renard.AlgebraicFamily.InducedTwistsDetection`. Internal helper for the
uniform induced-twist detector (`InducedTwistsUniformDetectionStatement`, Renard VI.8.4).

## Statement

`exists_fixed_of_normalizedJacquet_fixed`: let `G` be a locally compact nonarchimedean
group with closed subgroups `N` and `M`, where `M` normalizes `N`. Let `K` be a compact
open subgroup and `g ∈ G` with `Jacquet.IsIwahoriContraction K N M X g`. Let `D` be a
smooth complex representation with `D^K` finite dimensional. If the published normalized
Jacquet module `(normalizedJacquetFunctor N M).obj D` has a nonzero vector fixed by
`K ∩ M`, then `D` has a nonzero `K`-fixed vector.

This is the weak form of Jacquet's lemma (Renard VI.6.1, printed p.176 / PDF p.182) that
the detector needs. It needs no generation, admissibility or subquotient hypothesis on
`D`. Only `D^K` has to be finite dimensional. In the application `D^K = 0`.

## Proof

The normalization character `HaarModulus.closedInverseHalfCharacter N M` is trivial on
`K ∩ M` (`NormalizedJacquetBridge.character_trivial`, which uses compactness of `K ∩ M`).
So the normalized and unnormalized actions of `K ∩ M` agree
(`fixedVectors_twist_eq_of_le_ker`). The given vector is therefore fixed in the
localization model `Jacquet.Localization.action`. `Jacquet.Localization.trivialEquiv`
identifies that model with the actual Jacquet module `Jacquet.action D N M`. The proved
surjectivity `Jacquet.fixedJacquetMap_surjective_of_iwahoriContraction`
(`D^K → (D_N)^{K∩M}`, for an Iwahori contraction and finite-dimensional `D^K`) gives a
`K`-fixed preimage `d`. It is nonzero because its image is nonzero.
