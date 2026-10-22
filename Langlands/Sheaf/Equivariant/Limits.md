# Limits of actual equivariant topological sheaves

Author: Worker 13.

This module constructs limits in the published category
`Langlands.Sheaf.Equivariant.TopologicalSheaf G X A`. Its objects are actual
transport presheaves whose restriction to ordinary open inclusions is a sheaf.
The coefficient category `A` is arbitrary. For any index category `J` whose
limits exist in `A`, the corresponding limits exist in this equivariant sheaf
category.

The proof uses pointwise limits of functors. Restriction along the inclusion of
ordinary open subsets preserves limits. Mathlib proves that the ordinary sheaf
condition is closed under limits, and its inverse-image closure result transfers
this to the transport-sheaf property (`sheafProperty_closedUnderLimitsOfShape`).
Consequently the full-subcategory inclusion `toTransportPresheaf` creates
limits. No limit object or universal-property proof is assumed as an additional
field of an equivariant sheaf.

`transportLimit`, `transportLimitCone` and `transportLimitIsLimit` expose the
constructed object, its equivariant projection maps and its full universal
property. `toSheafForgetIso` records that forgetting equivariance and then the
sheaf condition is definitionally the same functor as forgetting the sheaf
condition and then the transport arrows. Since the latter preserves limits and
Mathlib's forgetful functor from ordinary sheaves on a topological space creates,
hence reflects, them, `toSheaf` preserves them. `underlyingLimitIso` then
identifies the underlying ordinary sheaf of the constructed limit with the
limit of the ordinary sheaves.

`evaluation` takes actual sections on an open subset. It preserves the same
limits. `limitSectionsIso` identifies sections of the constructed equivariant
limit with the limit of the section diagram. The transport operators are
inherited from the actual pointwise presheaf limit, so all group-labelled
naturality conditions remain part of the construction.

The common shapes are recorded as instances. Products of any size `w` exist
when they exist in `A` (`topologicalSheaf_hasProducts`), and likewise for
equalizers and finite limits. For a preadditive coefficient category with
equalizers, kernels exist (`topologicalSheaf_hasKernels`); the preadditive
structure is the published one on this category. If `A` has finite limits, then
sections over every open (`evaluation_preservesFiniteLimits`) and forgetting
equivariance (`toSheaf_preservesFiniteLimits`) are left exact. For example, for
`A = ModuleCat.{u} R` and a space in `Type u`, these instances supply products
indexed by the points of the space and kernels of equivariant sheaf maps.

The space, group, coefficient-object, coefficient-morphism, index-object,
index-morphism and product-index universes are explicit and independent. This
construction needs no group topology or continuity hypothesis: it uses the
already defined transport category and its ordinary open inclusions.

This is internal categorical infrastructure. Its direct mathematical provenance
is the pinned Mathlib implementations `CategoryTheory/Sites/Limits.lean`,
`Topology/Sheaves/Limits.lean`, `CategoryTheory/ObjectProperty/LimitsOfShape.lean`,
`CategoryTheory/Limits/FullSubcategory.lean`,
`CategoryTheory/Limits/FunctorCategory/Basic.lean` and
`CategoryTheory/Limits/Preserves/Basic.lean`, at commit
`5ed2965256430c3649e86755f9576b54eca72435`. Worker 13 read the relevant
construction, closure, creation and reflection proofs. The imported
equivariant sheaf category is published in Library commit
`30ceb5a0d89d8094c1663fc19f35416519b9a125` and is reused unchanged.

The purpose within the Harris framework is to provide real products and kernels
for subsequent equivariant constructions, in particular the product of
skyscraper sheaves in the equivariant Godement construction. This file does not
construct equivariant sheafification or cokernels, prove abelianness or enough
injectives, or identify ordinary-topological transport sheaves with Berkovich's
analytic equivariant site. In particular it supplies no acyclicity or derived
comparison.
