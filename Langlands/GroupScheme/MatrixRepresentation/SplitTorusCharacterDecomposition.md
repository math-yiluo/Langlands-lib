# Complete character-space decomposition for split-torus representations

Worker 1669.

This internal derivation proves that the actual universal character spaces span
any finite matrix representation of a supplied split torus over any field
`k : Type u`, with no characteristic or algebraic closedness assumption.
Together with the published `characterSpace_iSupIndep`, this gives the complete
character-space decomposition. The construction
`MatrixRepresentation.characterDecomposition` is the resulting linear equivalence
from the direct sum of the character spaces to the original coordinate space.
Its forward map is the canonical sum of submodule inclusions. Its inverse sends
a character vector to that vector in its own component and zero in every other
component, as proved by the accompanying evaluation lemmas.

The all-affine-test form of membership is equivalent to the universal equation:
the reverse implication evaluates at the universal affine point. Restriction of
a representation and character preserves character vectors, and restriction along
an actual group-scheme isomorphism identifies the character spaces.

For a standard split torus, the published
`GeneralLinear.CocharacterDiagonal.coefficientColumn_weight` proves that every
universal coefficient column is a vector for the corresponding exponent
character on every algebra. The published `span_coefficientColumn` says these
columns span the original coordinate space, so the supremum of its character
spaces is the whole space. Transport along the isomorphism supplied by
`IsSplitTorus` proves the general result
`MatrixRepresentation.iSup_characterSpace_eq_top_of_isSplitTorus`.

`SplitPinning.iSup_representationWeightSpace_eq_top` specializes this result to
the supplied torus of a split pinning, with exactly the weight spaces in the
published `IsHighestWeight`. It proves the decomposition conjunct for every
representation. It does not construct a representation of a prescribed highest
weight or prove irreducibility, the highest-space dimension, weight bounds, or
integral coroot generation.

The provenance is internal: this unit combines the existing all-algebra
coefficient-column construction, the actual exponent characters, the universal
character-space definition, and elementary submodule and isomorphism transport.
