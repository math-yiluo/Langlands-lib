# Filtered-colimit comparison for actual relative scheme points

The theorem `filteredRingPointComparison` proves exactly
`Langlands.AlgebraicGeometry.PointTopology.FilteredRingPointComparison`
from `FilteredRingPointStatement`. It retains its arbitrary common universe,
any commutative base ring, any small filtered algebra diagram with an actual
algebra-colimit witness, and an arbitrary relative scheme as target. There is
no affineness, quasi-compactness, quasi-separatedness or separatedness premise
on the target. The locally finite-type hypothesis is used for equality descent;
locally finite presentation is used for existence descent. This is a proof-only
module; it does not modify the statement or its imported constructions.

The source context is Brian Conrad, *Weil and Grothendieck approaches to adelic
points* (31 December 2011), printed pages 5–6, Theorem 3.4(1), Remark 3.5 and
(3.5.1), registered as `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The target's Markdown explains why the fixed-model formulation and weakened
hypotheses are a derived generalization. The implemented proof reuses pinned
Mathlib's scheme-limit results instead of reproducing Conrad's EGA references.

For both existence and equality, let `D` be the contravariant diagram of actual
relative spectra `F.op ⋙ algSpec R`, and forget its base to obtain `D₀` in
schemes. The natural transformation from `D₀` to the constant base scheme has
components the structure maps. Its naturality follows from the equations for
morphisms in the over category. Each source object is an actual affine spectrum,
so it is quasi-compact and quasi-separated; every transition map is the spectrum
of the indicated algebra homomorphism and is affine. Equality descent uses
quasi-compactness and affine transition maps; existence descent also uses
quasi-separatedness. These are source-diagram properties and impose no
restriction on the target scheme. The algebra-colimit
witness, `ringTestConeIsLimit`, and preservation of the connected limit by
`Over.forget` supply the actual limiting cone in schemes.

The private helper `pointColimit_injective` uses the same-stage filtered
colimit criterion
`Functor.CoconeTypes.descColimitType_injective_iff_of_isFiltered'`.
For two stage points whose images over the limit algebra agree, it projects
this equality to their underlying scheme morphisms. Their equations over the
base are exactly `Over.w`. Mathlib's
`Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType` gives a later spectrum
on which these underlying morphisms agree. Extensionality in the over category
turns this into equality of the actual changed-ring points. This establishes
injectivity of the existing `ringPointColimitMap` on its existing type-colimit
quotient, with no substitute point presentation.

The main theorem turns equality of images into equality of colimit classes
using that injectivity. The exact standard type-colimit criteria
`ιColimitType_eq_iff_of_isFiltered` and its same-stage variant identify equality
of classes with common-stage equality, or with equality after one common
transition arrow respectively. Their functor maps are definitionally the actual
`RingPoint.changeRing` maps. These equivalences prove both directions of each
explicit eventual-equality clause.

The private helper `exists_point_stage` applies
`Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation` to the underlying
morphism of a point over the colimit algebra. Its base-compatibility hypothesis
follows from `Over.w` for the cone legs and the point. The descended morphism
and the returned equation over the base define an actual stage point with
`Over.homMk`. The theorem's factorization equation, together with over-category
extensionality, gives exactly the required equality after change of value
algebra. The main theorem then represents a colimit preimage by this stage
point. Surjectivity follows, and locally finite presentation supplies locally
finite type for the already proved injectivity; their conjunction gives
bijectivity.

This fixed-model result does not prove existence or descent of models,
comparisons between varying models, descent of scheme properties, arithmetic
specialization to actual adelic rings, or any topology or model independence
of adelic points. It therefore covers the generic fixed-model comparison,
not all of Conrad's Theorem 3.4 or the full arithmetic assertion (3.5.1).
