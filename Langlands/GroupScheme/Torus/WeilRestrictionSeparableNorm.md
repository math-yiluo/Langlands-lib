# Finite-separable norm and scalar maps on Galois lattices

This internal comparison unit specializes the actual determinant norm and scalar
maps of `WeilGm` to the canonical finite-separable embedding decomposition. It
also constructs their intrinsic integer augmentation maps on the actual
cocharacter and character lattices.

The common setting consists of fields `k`, `K`, and `Ω` in one universe, a finite
separable extension `K/k`, and a `k`-algebra structure on `Ω`. The input `hsplit`
requires that every minimal polynomial of an element of `K` split over `Ω`.
No normality of `K/k`, algebraic closedness of `Ω`, or Galois hypothesis on
`Ω/k` is imposed. The automorphisms below are all `k`-algebra automorphisms of
`Ω`.

## Canonical norm and scalar coordinates

`separableEmbedding_tensorNorm` expresses the determinant norm of any element of
`K ⊗[k] R` as the product of its canonical embedding evaluations. Here `R` is
any commutative `Ω`-algebra, equipped with a compatible `k`-algebra structure
and scalar tower. It may be nonreduced or the zero ring.

`separableEmbedding_normHom_points` and
`separableEmbedding_scalarHom_points` identify the actual base-changed norm
and scalar morphisms on every test scheme over `Spec Ω`. The norm multiplies
the embedding coordinates; scalar inclusion sends a global unit to the
constant coordinate family. The morphisms are the existing
`decompositionNormHom` and `decompositionScalarHom`, with their canonical
comparisons to the base change of `G_m`. The conclusions use arbitrary test
schemes and global units, rather than only field-valued points.

`separableEmbeddingCharacterEquiv_normHom` and
`separableEmbeddingCocharacterEquiv_scalarHom` identify these actual morphisms
with the all-ones vectors in the canonical character and cocharacter lattices.
The two `separableEmbedding_galoisRepresentation_*` theorems prove that every
coefficient automorphism fixes the corresponding actual lattice element. The
proofs apply the previously established equivariant lattice equivalences:
inverse pullback permutes the embedding indices and preserves a constant vector.

## Intrinsic augmentations

`separableEmbeddingNormAugmentation` pairs an actual cocharacter with the actual
norm character. `separableEmbeddingScalarAugmentation` pairs an actual character
with the scalar cocharacter. They are integer linear maps to `ℤ`, constructed
from `latticePairing`, so their definitions do not depend on the chosen
splitting input. In fact these two definitions require only finite dimensionality
and the field structures; their coordinate and Galois comparisons use finite
separability and `hsplit`.

The two `*_eq_sum` formulas identify the augmentations with the sum of the
corresponding canonical embedding coordinates. Their
`*_galoisRepresentation` formulas prove equivariance for the trivial action
on `ℤ` by reindexing these finite sums. Finally,
`separableEmbedding_latticePairing_norm_scalar` identifies the pairing of the
norm character and scalar cocharacter with `[K : k]` as an integer: each
coordinate contributes one and the number of embeddings equals the extension
degree.

## Provenance and scope

This is a derived internal construction and comparison unit. The implemented
proofs specialize `WeilRestrictionNormSplit` along
`separableEmbeddingDecomposition`, use the canonical evaluation comparison in
`WeilRestrictionEmbeddings`, and use the actual permutation-action comparison in
`WeilRestrictionSeparable`. The degree computation uses that module's proved
embedding cardinality. No additional literature assertion or unproved
structural hypothesis is used.

This unit does not construct a norm-kernel group scheme, identify its lattices,
or classify subtori. Its Galois conclusions concern the ordinary actions on
the actual Weil-restriction lattices.
