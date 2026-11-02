# Spatial maps of equivariant Godement section cohomology

This is an internal construction derived from the existing spatial Godement
chain comparison and the global and compact-section functors. It supplies
spatial maps for the existing equivariant Godement section cohomology functors;
the comparison chain map is constructed from the spatial map itself.
No new attribution to an original literature definition is asserted here.

The namespace is
`Langlands.Cohomology.EquivariantGodementCohomology.Spatial`. Fix a commutative
ring `R`, a group `G`, topological `G`-spaces `X`, `Y` and `Z` with continuous
point translations, and a continuous equivariant map `f : X → Y`. The ring,
group, spaces and module carriers share a universe `u`, as in the existing
Godement complex and abelian equivariant sheaf category. The input sheaf `F`
is an equivariant sheaf of `R`-modules on `X`. No topology on `G` is required.

`globalComplexMap` is a natural transformation
`f_* ⋙ globalComplex_Y ⟶ globalComplex_X`. First take global sections of
`Godement.Spatial.complexNatTrans f hf`, whose component is
`Godement_Y(f_*F) ⟶ f_*Godement_X(F)`, then apply the existing global
direct-image identification. When `f` is proper, `compactComplexMap` uses
compact sections and the proved proper pullback of locally vanishing compact
sections in `LocalCompactComparison` in the same way. These are morphisms of
cochain complexes of algebraic `G`-representations and are natural in `F`.

`compactComplexMap_app` identifies the component with the general proper
compact chain pullback applied to the constructed spatial Godement chain map.
`compactComplexMap_apply` gives its underlying section in every degree: apply
the spatial chain map at the top open to the original section. In degree zero,
`compactComplexMap_apply_zero` identifies this with the actual
neighborhood-colimit stalk-family map `Godement.Spatial.zeroMap`.

`compactComplexMap_comparison` proves the square comparing the local-vanishing
and stalk-support conventions, using the existing compact-complex isomorphism.
`compactComplexMap_inclusion_triangle` says that forgetting support after
proper pullback equals forgetting support first and then applying the actual
global spatial map. `compactComplexMap_id` and `compactComplexMap_comp` prove
identity and contravariant composition for proper spatial maps, including the
direct-image sheaf on the intermediate space.

`globalCohomologyMap q` and `compactCohomologyMap hp q` apply the existing
homology functor in degree `q : ℕ` to those natural chain maps. Their sources
are respectively `f_* ⋙ globalCohomology_Y q` and
`f_* ⋙ compactCohomology_Y q`; their targets are the corresponding functors
on `X`. `compactCohomologyMap_app` identifies the component with the general
proper homology pullback of the actual spatial chain map. The accompanying
`_comparison` and `_inclusion_triangle` lemmas establish the support comparison
square and support-forgetting triangle on homology. The `_id` and `_comp`
lemmas prove identity and contravariant composition for proper maps.

The section formula is definitional; its degree-zero specialization rewrites
the proved degree-zero chain formula. The compact comparison squares and
chain-level support-forgetting triangle specialize the general results of
`LocalCompactComparison`. Chain identity and composition use the corresponding
proved spatial Godement laws and the general proper compact chain laws.
The homology triangle and functoriality laws follow by applying the homology
functor to these chain equalities and using its identity and composition laws.

These are ordinary topological equivariant sheaf constructions and the homology
of their Godement section complexes. There is no claim of acyclicity,
quasi-isomorphism, a derived-functor identification, smoothness of the resulting
representations, an etale or analytic realization, or an arithmetic/Harris
specialization. Those remain separate obligations. In particular the module
does not supply or assume an arbitrary higher comparison chain map as input,
and it does not identify these groups with Harris's cohomology.
