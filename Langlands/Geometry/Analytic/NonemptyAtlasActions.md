# Full categories of actions with nonempty supplied atlas charts

Author: Worker 56. Namespace: `Langlands.Analytic.NonemptyAtlasAction`,
with the property and category names in `Langlands.Analytic`.

Let `K : Type u` be a complete normed ultrametric field, and let
`M : Type z` be a monoid. The presentation universes are `u, v, w`.
`nonemptyAtlasActionProperty K M` requires that every chart of the
supplied categorical action have nonempty bounded multiplicative
spectrum. `NonemptyAtlasAction K M` is Mathlib's full subcategory for
this actual condition. Objects retain their supplied atlas action.
All complete equivariant chosen atlas arrows are morphisms; no extra
condition is imposed on maps. Charts may overlap or nest. An empty
space with no charts is allowed, since this condition is quantified
over its chart indices.

`inclusion` is the full and faithful inclusion into the original action
category. `normalize` lifts the existing `nonemptyActionFunctor` into
the full subcategory, using the proved nonempty-spectrum condition for
the actual same-space subatlas. Forgetting the condition gives exactly
that normalization functor.

For an object `X` of the full subcategory, every original chart survives.
`normalizationIso X` is constructed from the existing `nonemptyIso` on
the underlying presentation and the complete equivariance equation
for the original inclusion. Its forward arrow is that inclusion, and
its inverse is the existing `nonemptyInv` using `X.property`. Both maps
are the identity on the original point space. The inverse sends each
original chart index `i` to `⟨i,X.property i⟩` and uses the bounded
identity on its original algebra.

Full-arrow naturality of the inclusion proves
`normalizationIso_naturality`. `normalizationNatIso` packages these
isomorphisms between inclusion followed by normalization and inclusion.
Naturality of its inverse proves `normalizationIso_inv_naturality`,
again as an equality of entire equivariant arrows with their chosen
chart maps and bounded pullbacks.

For any monoid homomorphism `φ : N →* M`, `restrict φ` lifts the existing
action restriction to these full subcategories. Its underlying
presentation and every underlying bounded map are retained exactly,
so the same nonempty-chart proof applies.

The provenance is internal: this bundles the previously constructed
same-space nonempty-chart normalization, its conditional bounded
isomorphism and its proved full-arrow naturality using Mathlib's
full-subcategory and action constructors. It assumes no inverse to
normalization outside the stated chart condition. No topology on the
acting monoids, analytic automorphism continuity, induction adjunction,
refinement localization or analytic site is constructed in this module.
