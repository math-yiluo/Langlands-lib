# Recovering apartment facets from actual model images

This internal derived module combines the published sharp-fixer apartment
fixed-locus theorem with facet constancy, containment in the unramified zero
subgroup, and exact schematic-image order recovery. All declarations retain
arbitrary universe `u`. The module translates no new external literature claim.

In `Langlands.Geometry.Building.KPApartmentData`,
`isFaceOf_of_sharpFixer_le_pointwiseFixer` works over any field with a connected
reductive group, a maximal split torus and its actual apartment data. It
assumes AS4: every extended affine root is an affine root or twice it is one.
Let `Ω` and `Ω'` be nonempty subsets of full apartment facets `Fa` and `Ca`.
If the actual sharp fixer of `Ω` fixes the apartment image of `Ω'` pointwise,
the conclusion is `AffineRootSystem.IsFaceOf D.affineRoots Ca Fa`.

The proof chooses `x ∈ Ω` and `y ∈ Ω'`. Facet constancy identifies the sharp
fixer of `{x}` with that of `Fa`; antitonicity puts it in the sharp fixer of
`Ω`. Hence it fixes the image of `y`. The published
`mem_facetClosure_of_fixed_by_sharpFixer` places `y` in the formal affine-root
closure of the facet of `x`. The full-facet partition and
`facet_subset_facetClosure_iff` then give the asserted face incidence.

Now fix a nonarchimedean local field `F`, a supplied affine group `H` over its
maximal unramified field, `C : MaximalUnramified.BuildingData F H`, and
`E : UnramifiedZeroDatum F H`. The building data carry connected reductivity
and maximal splitness and prove AS4. Every sharp fixer lies in `E.zeroPoints`
by `sharpFixer_le_zeroPoints` and fixes its own subset. Consequently
`UnramifiedZeroDatum.isFaceOf_of_zeroFixer_le` reflects inclusion of the
actual subgroups
`E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω)` into the same
reverse face incidence, for nonempty subsets of full facets.
`facet_eq_of_zeroFixer_eq` applies the reflection in both directions and
uses antisymmetry of affine face incidence.

The construction `UnramifiedZeroDatum.facetZeroFixerEmbedding` in
`Langlands.Geometry.Building` sends each full facet of this displayed
apartment to its actual zero-fixer subgroup of `rationalPoints H`, taking
`Ω` to be the full facet. The preceding equality criterion proves
injectivity. Its application theorem is definitional. No identification of
zero fixers with sharp fixers is assumed.

Finally, in `Langlands.BruhatTits.IntegralModels`, let `R` be a Henselian
local domain with fraction field the maximal unramified field and
algebraically closed residue. Let `source₁`, `source₂` and `target` be actual
relative-component model pairs for `H`, with identity-generic morphisms
`φ` and `ψ` from these sources to the common target. These model pairs
carry smooth affine full and neutral models of finite type, and connected
neutral fibres. Assume their neutral integral-point subgroups equal the
two actual zero fixers above, and that the target neutral congruence subgroup
is contained in each source neutral integral-point subgroup.

`isFaceOf_of_unramifiedSpecialFibreImage_le` proves that containment of
`SubgroupFunctor.range φ.specialFibreImageInclusion` in
`SubgroupFunctor.range ψ.specialFibreImageInclusion` on every residue-scheme
test forces `Ca` to be a face of `Fa`.
`facet_eq_of_unramifiedSpecialFibreImage_eq` recovers `Fa = Ca` from
equality of those actual schematic-image subgroup functors. The proofs
use the exact image-order or image-equality criterion from
`SpecialFibreImageRecovery`, rewrite by the integral-point characterizations,
and apply the geometric zero-fixer results.

The facets and subsets in these results lie in the same displayed apartment.
The model-image results retain the explicit characterizations and congruence
containments. They do not establish these inputs for all facet models,
descent to facets over `F`, parabolicity, surjectivity onto parabolics, or
the host `UnramifiedFacetParabolicOrderStatement`.
