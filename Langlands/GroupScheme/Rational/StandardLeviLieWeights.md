# Selected-root weight spaces in an actual standard Levi

This internal supporting result uses the existing all-test `standardLevi`, its
actual torus factor, the actual Lie-kernel differential, and the published
proposition `DynamicLieStatement`. The latter is retained as an explicit
premise; this module does not prove that proposition.

For any represented subgroup, the image of the differential consists exactly
of the ambient tangent vectors whose dual-number points belong to the subgroup
functor. The proof lifts that point using the representing equivalence and
checks its reduction is the identity by canceling the representing
monomorphism.

For a character in the selected set `J`, every defining standard cocharacter
pairs to zero with it. Restricting its ambient weight space to each such
cocharacter gives weight zero. The centralizer clause of `DynamicLieStatement`
places the corresponding dual-number point in every defining centralizer and
hence in `standardLevi`. The preceding tangent-image criterion lifts it to the
actual representative. Preservation and reflection of weights by the
injective differential identify this selected-character weight space with the
ambient one. `standardLeviWeightSpaceEquiv` packages this identification as a
linear equivalence whose underlying map is the actual differential
`Lie.targetMapLinear j k`, as recorded by its coefficient formula. If `J`
consists of simple relative roots, their nonzero ambient
weight spaces therefore remain nonzero in the representative.

The field and universe are arbitrary. The argument needs the ambient affine
group scheme to be locally of finite type and the representative to be affine;
it assumes neither reductivity of the representative nor reducedness of the
relative root system, splitness, a positive rank, or existence of a standard
cocharacter. Finiteness and standard-cocharacter existence are not needed
because membership in the Levi uses the defining intersection directly.

This is derived from published definitions and the explicitly retained dynamic
Lie premise. It does not establish standard-Levi reductivity, the converse
description of its roots, or the split-component central-direction theorem.
