# Actual Picard chart lifting at a specified residue-field map

This is an internal construction from the actual Picard pseudofunctor,
its actual point-fibre presheaves, the augmented Artinian tests, and
pointed deformations. The composition and elementary-surjection arguments
specialize the existing `ArtinianChartLifting` construction while retaining
a specified residue-field map. The realization argument uses only the
actual augmentation and the given lifting property.

Fix a commutative ring `k`, a field `k`-algebra `K`, a scheme map
`f : X ⟶ Spec k`, a scheme `U` over `k`, a line bundle `L` on
`U ×_k X`, and a map `p : Spec K ⟶ U` over `k`. All types retain an
arbitrary universe `u`. The constructions require no properness or
finite-type hypothesis.

`FiberPoints f L M Z` is the existing actual fibre-point type. A point
contains a map from the test scheme to `U` and an isomorphism between
the pullbacks of the actual bundles `L` and `M`. It retains the full
isomorphism, including its automorphisms.

For an augmentation-preserving algebra arrow `q : A ⟶ B`,
`HasLiftingForAt f L p q` requires lifting of every actual fibre point
on `B` whose composite residue map is `p`. The quantifiers include every
scheme `T` over `k`, every bundle on `T ×_k X`, and every pair of
compatible maps from the spectra of `A` and `B` to `T`. The lifted
point restricts to the specified point as an equality in the actual
fibre-point type. `residueMap_of_restrict_eq` uses the augmentation
triangle to show that such a lift has the same residue map;
`exists_lift_at` exposes this equality.

`IsFormallyVersalAt f L p` is the proposition that this lifting property
holds for every surjective arrow of the augmented local Artinian
`k`-algebras with residue field `K`. This is the internal lifting
condition at the specified map `p`; no additional restriction on that
point, such as finite residue degree, is implicit in the name.

`hasLiftingForAt_comp` lifts first through the second arrow and then
through the first. The residue-map lemma makes the intermediate lift
eligible for the same condition at `p`. Coherent restriction of actual
point fibres shows that the final point has the required restriction.
`isFormallyVersalAt_iff_elementary` then applies the published Artinian
surjection induction. Here elementary means a surjection whose kernel
is annihilated by the source maximal ideal, including a zero kernel.
The criterion retains the original chart maps and bundle isomorphisms.

`hasLiftingFor_iff_forall_at` and
`isFormallySmoothOnTests_iff_forall_versalAt` identify the existing
all-test lifting condition with its conjunction over all specified
residue maps into the same family. In the reverse direction the residue
map of the given point supplies `p`; no choice of a new family occurs.

For actual deformation realization, `residueBundle f L p` is the
ordinary pullback of `L` at `p`. An object `N` of
`ArtinianTestDeformations.Deformations f (residueBundle f L p) A`
contains an actual bundle on `Spec A ×_k X` and a specified isomorphism
from this residue bundle to its reduction. `augmentationArrow A`
is the arrow from `A` to the identity-augmented residue test; its
spectrum map is exactly the prescribed residue inclusion.
The residue test itself has the identity residue inclusion.
`residuePoint f L p A N` pairs `p` with the very same specified
isomorphism of `N`, regarded as an isomorphism in the Picard groupoid.

`exists_realization_point` applies formal versality to this surjective
augmentation. It returns an actual point `x` over the identity map of
`Spec A`, with residue map `p`, whose restriction equals
`residuePoint f L p A N`. Thus the result realizes every such pointed
deformation and preserves its complete prescribed reduction
isomorphism. `realizationIso` composes the isomorphism of `x` with the
actual relative pseudofunctor identity comparison and forgets the core
notation. Its result is an ordinary bundle isomorphism from the pullback
of `L` along `x.1` to the underlying bundle of `N`.

The Artinian tests retain their original `k`-algebra structure and a
surjective augmentation to `K`; no section or `K`-algebra structure on a
general test is imposed. This module does not construct a formally
versal family, a hull, effectivity, algebraization, openness of
versality, or a smooth scheme atlas. Those existence and geometric
steps remain separate obligations for the field Picard stack atlas.

The unchanged `augmentationArrow` definition is imported from
`Deformation/ArtinianAugmentationArrow`; its namespace and interface are preserved.
