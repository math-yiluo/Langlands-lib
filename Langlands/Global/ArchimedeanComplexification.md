# Complex matrices for the actual archimedean group

The namespace is `Langlands.Global`. For every number field `K : Type u` and
every natural rank `n`, this module constructs the direct sum of its standard
local complex matrix representations. The local real matrices are included in
complex matrices by the usual inclusion of real entries, and the local complex
matrices retain their entries. The construction is faithful, continuous, and a
closed embedding into complex GL. It also carries the published standard
infinite compact subgroup into the complex unitary group.

## Coordinates and algebra

`ArchimedeanPlaceIndex K` is the disjoint sum of the real infinite places and the
complex infinite places. `archimedeanPlaceEmbedding K v` evaluates the mixed
coordinate ring at that place, composing with the real-to-complex inclusion at
a real place. It is a real algebra homomorphism; its additivity, multiplicativity,
identity, and scalar compatibility are proved directly. This definition itself
requires only a field.

For a number field, `ArchimedeanComplexIndex K n` is
`Fin n × ArchimedeanPlaceIndex K`. Both factors are finite. In particular, the
index is empty when `n = 0`; no nonempty or positive-rank assumption is imposed.

`archimedeanLocalMatrices K n` applies each place embedding entrywise.
`archimedeanComplexification K n` assembles these matrices using Mathlib's
`Matrix.blockDiagonal`. It is a real algebra homomorphism from the actual
`ArchimedeanMatrix K n` to complex matrices on the new index. The exact entry
formula is

```
C(A)((i,v),(j,w)) = if v = w then placeEmbedding(v)(A(i,j)) else 0.
```

Theorems `archimedeanComplexification_apply`,
`archimedeanComplexification_real`, and
`archimedeanComplexification_complex` give the full and diagonal-block formulas.
The source algebra is real because the real-place blocks are not complex
algebras. Every output matrix nevertheless acts complex-linearly on the usual
complex coordinate space.

## Topology and faithfulness

`archimedeanComplexification_injective` recovers every real and complex entry
from the diagonal blocks. Injectivity of the usual real inclusion recovers the
real entries. This proof is valid even at rank zero.

`isClosedEmbedding_archimedeanComplexification` uses the real-linear map
underlying that algebra homomorphism. Its domain is a finite-dimensional
Hausdorff real topological vector space, so Mathlib's
`LinearMap.isClosedEmbedding_of_injective` proves the embedding and its closed
range. The argument uses existing product topologies; it introduces no closure
assumption or extra norm.

`archimedeanComplexGL K n` is the induced homomorphism on units. The theorem
`isClosedEmbedding_archimedeanComplexGL` follows from Mathlib's closed-embedding
result for `Units.map`, which controls both the matrix and its inverse.

`infiniteAdelicComplexGL K n` composes this map with the published continuous
multiplicative equivalence `archimedeanGLCoordinates K n`. Its domain is exactly
`Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing K)`, with the
original completion-product topology. The map is bundled as a continuous
monoid homomorphism. `infiniteAdelicComplexGL_val` identifies its value matrix,
and `isClosedEmbedding_infiniteAdelicComplexGL` proves the closed embedding.
Thus it is a genuine faithful finite-dimensional complex matrix representation.

The last closedness claim is in **complex GL**. Its image in the full matrix
endomorphism space is not asserted to be closed. Adding the inverse-adjoint and
trivial blocks is a separate construction supplying that stronger property.

## Coordinate square formula

`archimedeanComplexification_sum_sq` proves

```
sum a,b ‖C(A)(a,b)‖² =
  sum real v, i,j ‖A(i,j).real(v)‖² +
  sum complex v, i,j ‖A(i,j).complex(v)‖².
```

The proof expands the block formula, sums away the off-diagonal zeros, exchanges
finite sums, and uses preservation of the absolute value by the real inclusion.
`infiniteAdelicComplexGL_sum_sq` gives the same identity directly for the actual
completion-based group, using the published `ArchimedeanGL.realMatrix` and
`ArchimedeanGL.complexMatrix`. Applying it to `g⁻¹` gives the inverse-entry
formula. These are finite sums of scalar norms, independent of a chosen norm
instance on the full matrix algebra.

## Standard compact invariance

`archimedeanComplexGL_mem_unitaryGroup` proves that orthogonal real local blocks
and unitary complex local blocks give a unitary complex block matrix. It expands
block conjugate transpose and block multiplication. In a real block,
conjugate transpose of the included matrix is the inclusion of its real
transpose. Mapping the real orthogonality equation through the entrywise real
inclusion gives the required complex unitary equation. Complex blocks already
satisfy that equation.

`infiniteAdelicComplexGL_mem_unitaryGroup` obtains exactly those local hypotheses
from `mem_standardInfiniteCompact_iff`. Its hypothesis uses the actual published
`standardInfiniteCompact K n`; no arbitrary subgroup or invariance certificate is
supplied. Matrix unitarity refers to the standard Hermitian structure on the
complex coordinate space. The later Hilbert-space specialization uses Mathlib's
Euclidean space with this structure.

## Source and derived provenance

A. Borel and H. Jacquet, *Automorphic forms and automorphic representations*,
Corvallis (1979), §1.2, printed pp.189–190 (one-based PDF184–185), defines a group
norm from a finite-kernel complex representation whose image is closed in
`End(E)`, with a compact-invariant Hilbert structure. Its inverse-dual remark
explains adding the representation `g ↦ σ(g⁻¹)*`. Section 4.2(d), printed p.195
(PDF190), later uses slow growth on each finite adelic slice.

The registered source is `borel-jacquet-1979-automorphic`, the original Part I PDF
with SHA256
`3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
The cited original pages were read. No source erratum is present in the project
errata notes or the retained Corvallis source folder.

This module is a derived, explicit prerequisite for that norm. The source is not
claimed to contain this particular indexed Lean construction or its proofs.
The module reuses the published actual archimedean coordinates and standard
orthogonal/unitary compact, together with Mathlib's block matrices and
finite-dimensional topology. It does not yet define the final Hilbert-Schmidt
group norm, prove maximal compactness, compare growth norms, or construct
automorphic forms. Those conclusions require the subsequent constructions.
