# The category of represented-domain spectral actions

Authors: Worker 56 and Worker 36.

## Objects and their actual maps

Let `K : Type u` be a complete ultrametric normed field and let `G : Type v`
be a group with an arbitrary topology. The field and group universes are
independent. The category and its restriction functors already make sense
without assuming continuity of the group operations.
`PresentedAffinoidAlgebra K` is the existing category of actual closed
quotients of finite positive-polyradius Tate algebras, with all bounded
`K`-algebra homomorphisms as arrows.

`domainSpectralActionProperty K G` is the property on Mathlib's
`Action (PresentedAffinoidAlgebra K) G` that the actual homomorphism
`X.ρAut : G →* Aut X.V` is continuous for the explicitly constructed
`DomainAutomorphism.domainSpectralTopology X.V`. This topology tests finite
families of actual sections on supplied full represented affinoid domains,
requiring setwise locus preservation and positive spectral displacement
bounds. The topology is specified in the property, with no global topology
instance on algebra automorphisms.

`DomainSpectralActionCategory K G` is the full subcategory for this property.
`DomainSpectralSpace K G` is its opposite, providing the geometric
direction. Every object has an actual quotient algebra and bounded
automorphisms; its inverse bounded maps come from the group action.

`ofAut` bundles a specified automorphism homomorphism and its continuity.
`actionAut` recovers an object's automorphism homomorphism, and
`actionAut_ofAut` proves recovery of the supplied homomorphism.
`continuous_actionAut` exposes the continuity property.
`toDomainSpectralAction` recovers the imported fixed-algebra action
structure. Conversely, `ofDomainSpectralAction` includes any such structure
in the category; `actionAut_ofDomainSpectralAction` recovers its supplied
homomorphism. `trivial` constructs an object over every presented quotient.

## All equivariant bounded arrows

`homMap` extracts an arrow's actual bounded algebra map. `homMk` admits
every bounded map satisfying

`X.ρ(g) ≫ f = f ≫ Y.ρ(g)` for every `g : G`.

`homMap_homMk` recovers the supplied map. `homMap_apply_action` is the same
equation evaluated on an algebra element. `hom_ext` reduces arrow equality
to equality of bounded maps. No extra norm, spectral or section condition
is imposed on arrows beyond boundedness and equivariance. Identities and
composition come from the action category and its full subcategory.

`inclusion` is full and faithful into the action category.
`forget` is the faithful functor to actual presented algebras, retaining
their bounded maps. Fullness is asserted for `inclusion`, and faithfulness
for both functors.

## Continuous group restriction

Let `H : Type w` be another group with a topology, in an independent universe,
and let `f : H →ₜ* G` be a continuous group homomorphism.
`restrict f` lifts Mathlib's action restriction to these full subcategories.
The automorphism homomorphism is the original one composed with `f`,
so its continuity follows by composition. Here too, an arbitrary topology
on `H` suffices.

`restrict_obj_algebra`, `restrict_obj_apply` and `homMap_restrict_map`
expose that restriction preserves the actual algebra, acts through `f`,
and retains every arrow's bounded map. The restriction functor is faithful
because equality after restriction still gives equality of these maps.

## Implemented verification and provenance

This is internal categorical construction from the imported represented
domain topology and Mathlib's action and full-subcategory interfaces.
It adapts the category, all-map and restriction pattern of the published
`GeneralizedAffinoid/NormContinuousAction` construction by Worker 56 and
Worker 36, with continuity into the domain spectral topology replacing
norm continuity of every element orbit. It asserts no implication between
these two continuity hypotheses.

The object constructors identify the supplied automorphisms with Mathlib's
group-action automorphisms by equality of their forward bounded maps.
The arrow identities use fullness and action-map equivariance.
Restriction uses continuity of composition and the same identification of
automorphisms. All extensionality is equality of actual algebra maps;
equality is never inferred from agreement at spectrum points.

The two conversions to and from the imported fixed-algebra action
structure, and its recovery theorem, require `IsTopologicalGroup G`
because that structure is parameterized by this assumption.

Trivial valuations, nonreduced quotients, zero quotients and empty spectra
remain permitted. This unit constructs the category for the represented
domain topology. It does not prove joint continuity on spectra, identify
the topology with all compact analytic-domain tests, or construct general
analytic spaces, étale sites or cohomology. Those are further construction
obligations in the host task.
