# The intrinsic global transpose pairing from factor forms

This internal construction for Task 7294 assembles an actual finite
adelic transpose pairing and a full archimedean transpose pairing into
the intrinsic pairing on the original automorphic realization.

Let `A` be an actual nonzero irreducible admissible subrepresentation
of the finite adelic action of an irreducible full operator realization
`S`. The implemented finite-factor evaluation is a linear equivalence
from `A` tensor its full multiplicity space onto `S.Space`. Given a
nonzero inverse-transpose bilinear form on `A` and a nonzero bilinear
form on the multiplicity space satisfying the full compact and global
complexified Lie identities, `finiteInfiniteTransposePairing` tensors
the two forms and transports the result along this equivalence.

The resulting form is nonzero by the proved tensor-form nonzeroness
and transport lemmas. Finite adelic invariance uses evaluation
covariance on the first factor. Compact invariance and Lie
skew-invariance use covariance on the second factor. Restricting the
complexified Lie identity to the actual real Lie algebra gives exactly
the infinitesimal clause of `S.IsTransposeInvariantPairing`, including
the prescribed global negative transpose.

`PlaceDensityModels.fullTransposePairing` supplies the multiplicity
form from the preceding actual archimedean source-model construction.
Its inputs remain nonzero forms on the finite factor and on all
chosen real and complex source models. No existence of these forms
is claimed here. In particular, this implemented assembly does not
by itself prove the unconditional contragredient target.

The provenance is internal. The proof uses the completed evaluation,
tensor pairing transport, actual local-model assembly, and the
Library's intrinsic transpose-pairing definition.
