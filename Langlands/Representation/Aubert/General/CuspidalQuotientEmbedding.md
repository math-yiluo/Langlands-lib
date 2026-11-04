# Irreducible inducing quotients and preservation of cuspidality

This internal supporting unit factors the quotient and adjointness steps of
`RationalCuspidalEmbeddingProof` and `RationalLeviCuspidalJacquet` away from the
actual rational-point subgroup expressions. It retains every compactness and
unimodularity input.

`IsCuspidalFor.of_surjective` uses the published surjectivity of normalized
Jacquet maps to transfer subsingleton Jacquet modules to a quotient.
`IsLeviCuspidal.of_surjective` specializes this argument to the proper standard
parabolics inside a closed Levi. `nontrivial_pullback` records that the smooth
pullback along a continuous group equivalence has the same vector carrier.

The entry definition `adjointOfJacquetMap` exposes the actual smooth morphism
given by the inverse of `General.FirstAdjointness.equiv`.
`adjointOfJacquetMap_injective` proves it injective when the source is
irreducible and the Jacquet morphism is surjective onto nonzero data: the
adjoint cannot vanish because the adjointness equivalence would then make the
surjection vanish, and a nonzero map from an irreducible object is injective.
This factors the argument in the published
`embedding_of_surjective_jacquet_map` through a named morphism.

`exists_irreducible_quotient_embedding` starts with an irreducible smooth
representation and a nonzero Jacquet module. Compactness of the literal left
parabolic quotient gives finite generation of the Jacquet module by
`JacquetFiniteGeneration.finite_of_compactQuotient`. The existing coatom quotient
construction gives an actual irreducible smooth quotient. Its pullback to an
identified Levi is irreducible, using
`isIrreducible_comp_continuousMulEquiv_iff`. The surjection pulls back with its
same linear map. The named adjoint and its injectivity theorem give the
induction embedding with the explicit unimodularity premise.

The conclusion exposes both the surjective map from the flattened Jacquet
module and the actual induction embedding. This allows a later consumer to
transfer cuspidality without repeating the quotient construction. The carrier
size is `max uG uV` as required by the actual induction functor. This supporting
unit does not itself prove the full support-category vanishing target.
