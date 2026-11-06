# Coroot inheritance for the same actual torus in a subgroup

Authors: Worker 1577.

This internal construction compares supplied actual integral root data for one
commutative group scheme `T` embedded in two affine group schemes over a field.
The subgroup torus map `iH : T.toGrp ⟶ H` factors the ambient map `i` through an
actual homomorphism `j : H ⟶ G`. The underlying ambient torus map is a
monomorphism, and its full Weyl image is finite. The result does not require the
subgroup root datum to have the same root range as the ambient datum and does
not regard it as an actual root datum of `i`.

The generic uniqueness lemma first considers an actual ambient normalizer point
acting on the character lattice by the reflection formula along `P.root p`, with
an integral cocharacter pairing to two. The supplied actual datum realizes its
own reflection by another actual normalizer point. Both actions belong to the
finite full Weyl image, so their product has finite order. The published internal
lemma `Langlands.LinearAlgebra.eq_functional_of_finiteOrder_reflections` identifies
the two defining integral functionals. Perfectness of the supplied root datum's
pairing then identifies the cocharacters. This argument uses neither a
root-spanning hypothesis nor reductivity of the subgroup.

`IsRootDatumOf.coroot_eq_of_normalizing_latticeReflectionIso` applies this
uniqueness to the explicit torus involution `latticeReflectionIso`. Its hypotheses
retain an actual normalizing point, the pairing-to-two equation, a supplied
actual root datum, and finiteness of the ambient full Weyl image. It supplies no
independent existence theorem for that normalizing point.

For the same torus in a subgroup, each normalizer point realizing a subgroup
reflection maps under `j` to an actual ambient normalizer with the same torus
automorphism. The published `IsNormalizingPoint.comp` implements this
transport. The uniqueness lemma therefore proves that equal roots in the two
supplied actual root data have equal integral coroots.

`SameTorusRootDatumEmbedding P R` packages an embedding of the subgroup root
indices into the ambient indices together with equality of both roots and
coroots. `IsRootDatumOf.sameTorusSubgroupEmbedding` constructs it from the actual
factorization and root-support inclusion. Its `corootSpan_eq` theorem turns a
root-support equality `Set.range R.root = P.root '' s` into the integral equality
`R.corootSpan ℤ = Submodule.span ℤ (P.coroot '' s)`.

The provenance is an internal derivation from the published root-datum/Weyl
comparison and actual normalizer transport interfaces. No new geometric
hypothesis is asserted as a theorem. In particular, the construction does not
prove root-datum existence, Weyl-image finiteness, a comparison for different
tori, or the full derived-centralizer target.
