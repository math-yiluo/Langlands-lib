# Full kernels for characterized descended incident facet models

This is an internal geometric reduction for the actual descended facet models
in `UnramifiedFacetParabolicImageStatement`, at arbitrary universe `u`. Its
provenance is the imported Library constructions and lemmas. It introduces no
new interpretation of the original literature.

`IncidentFacetKernelChart` records one original rational translation and two
subsets of the actual maximal-unramified apartment. The lower subset is
nonempty, every real affine functional is bounded above on the upper subset,
and the lower subset lies in the ordinary topological closure of the upper
subset for the initial topology of all real affine functionals. The two chart
images are exactly the images under the supplied building map `e` of the
original incident facets.

`incidentFacetKernelChart` constructs these data from any downstairs
`ValuationBuildingData B`, maximal-unramified building data `C`, building map
`e`, affine apartment map `a`, and incident downstairs facets. It requires just
three of the apartment-descent hypotheses in `UnramifiedFacetParabolicImageStatement`: equivariance
of `e` under rational extension, compatibility of `e` and `a` on the displayed
apartments, and the exact restricted-facet preimage identity. It needs none of
the seven additional building predicates of that statement.

The construction unpacks `FacetPrecedes` to obtain a common translated
downstairs chart and apartment facets `Fa` and `Ca`, with `Fa` a face of `Ca`.
Its upstairs subsets are precisely `a '' Fa` and `a '' Ca`. The restricted-facet
identity puts the upper subset in one full upstairs facet. The published
bounded-facet theorem, applied to the nontrivial normalized valuation of the
maximal unramified extension, bounds every affine functional on that full
facet and hence on the upper subset.

The closure proof uses the original subsets themselves. For a point `q` of the
combinatorial closure of the facet through `p`, the published lemma
`AffineRootSystem.lineMap_mem_facet_of_mem_facetClosure` places
`lineMap q p t` in that facet whenever `0 < t ≤ 1`. Applying `a` gives points of
its actual image. The resulting curve tends to `a q` as `t` tends to zero from
above: composition with every real affine functional is a continuous affine
function of `t`, which proves continuity for the specified initial topology.
Thus the image of the closed facet lies in the topological closure of the
image of the open facet. The original face inclusion yields the required
closure relation for `a '' Fa` and `a '' Ca`. Equivariance and apartment
compatibility give the two translated image equalities.

`unramifiedFacetKernel_of_modelKernel` takes
`UnramifiedModelKernelStatement` as an explicit premise. In addition to the
three map hypotheses above, its inputs are an actual zero datum `E`, incident
facets, arbitrary relative-component model pairs `D` and `D'`, their two exact
unramified integral-point characterizations, and any model morphism
`φ : RelativeComponentModelHom D' D`. Its conclusion is exactly
`φ.HasSmoothConnectedUnipotentKernel`, for the entire scheme-theoretic kernel
of the neutral special-fibre map.

The proof applies the full-kernel premise directly to the actual
`baseChangeUnramified` models. The chart supplies nonemptiness, boundedness and
ordinary topological closure; the two model characterizations supply its
integral-point hypotheses. The stored neutral smoothness of the supplied model
pairs gives smoothness after coefficient extension. The upstairs map is the
actual `Hom.baseChangeUnramifiedId` of `φ.neutral`. Finally,
`Hom.specialFibreKernel_properties_of_baseChange` reflects smoothness,
connectedness and unipotence through the actual residue-field extension.
The three local integer-algebra instances have explicit names so that this
module can be combined with other unramified comparison modules.

This module discharges the facet-specific geometric hypotheses needed
to consume the full-kernel statement. It does not prove that statement,
parabolicity of the special-fibre image, the reduction-preimage equality, or
`UnramifiedFacetParabolicImageStatement`.
