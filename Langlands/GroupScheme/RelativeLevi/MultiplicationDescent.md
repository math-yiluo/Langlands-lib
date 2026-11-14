# Smoothness and multiplication descent for Levi subgroups

This derived construction supplies two descent steps for relative Levi
subgroups over an arbitrary scheme. It uses the Library's actual
`subgroupMultiplication` morphism, with the Levi factor first, in the category
of schemes over the base.

`property_of_etaleCover` proves that a morphism property which is Zariski local
at the target and descends along surjective flat locally finitely presented
morphisms can be checked on an arbitrary étale covering family. The base and
the covering index type are in universe `u`. The proof forms the coproduct of
the cover members. Its map to the base is étale and surjective. The canonical
open cover of that coproduct reduces the pulled-back property to the given
local properties, using the pullback pasting isomorphism. Descent along the
single coproduct map then proves the original property.

`smooth_of_etaleCover` applies this argument to the structural map of a group
scheme. Thus smoothness of every pulled-back group scheme implies smoothness
of the original group scheme.

`isPullback_over_baseChange` verifies the underlying cartesian square for the
base change of any morphism of schemes over the base. `isIso_of_etaleCover`
then tests an arbitrary relative morphism for isomorphy on an étale cover of
the base. It pulls that cover back to the target of the morphism, compares
the two pullback constructions, and applies the preceding property descent
to the underlying scheme morphism. The forgetful functor from relative
schemes reflects isomorphisms.

`subgroupMultiplication_baseChange` identifies base change of multiplication
with multiplication of the base-changed subgroup maps. Its domain comparison
is the canonical product isomorphism of the pullback functor. The proof uses
preservation of multiplication on morphisms and the two projection identities
for that product comparison. In particular,
`subgroupMultiplication_isIso_baseChange` preserves isomorphy under arbitrary
base change.

`subgroupMultiplication_isIso_of_etaleCover` descends isomorphy of this
multiplication map from an étale covering family.
`subgroupMultiplicationIsoOfEtaleCover` returns the resulting actual
isomorphism of relative schemes
`L.X ⊗ U.X ≅ P.X`. Its forward morphism is exactly
`subgroupMultiplication l r`, as recorded by the accompanying `_hom` lemma.
The inputs are global group schemes `L`, `U`, `P`, global group homomorphisms
`l : L ⟶ P`, `r : U ⟶ P`, and isomorphy of multiplication after every member
of the specified étale cover. No closedness, normality, smoothness, affineness,
or radical hypothesis is needed for this isomorphism construction.

Finally, `isRelativeLeviSubgroup_of_etaleCover` packages the result when `l`
is already a closed subgroup and `r` is already a relative unipotent radical.
Smoothness of `L` and the isomorphism condition on the multiplication may be
supplied locally on the étale cover. The conclusion is the existing
`IsRelativeLeviSubgroup l` predicate, with the supplied `r` as its radical
witness.

The provenance is internal: these constructions combine Mathlib's morphism
property descent and cartesian monoidal pullback interfaces with the Library's
relative Levi predicates. They introduce no independent assertion from
external literature. They do not construct the global subgroup maps or their
radical property, and do not prove the maximal-torus Levi existence or
uniqueness statement.
