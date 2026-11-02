# Proper spatial maps on complexes of full equivariant compact sections

This internal construction applies the actual functors from
`Langlands.Sheaf.Equivariant.LocalCompactSections` and
`Langlands.Sheaf.Equivariant.ProperCompactSections` term by term to supplied
complexes. It constructs chain maps and their induced homology maps.

The spaces have universe `u`, the group `v`, the commutative coefficient ring
`r`, coefficient modules `w`, and the arbitrary complex index `t`. These
universes are independent. Individual group translations on each space are
continuous; the spatial map is continuous and equivariant, and compact spatial
pullback additionally requires `IsProperMap`. No topology on the group or
coefficients is used.

The three local-section functors and the full direct-image presheaf and sheaf
functors are additive: each sends a sum of morphisms to the pointwise sum on
the original sections. Mathlib's `mapHomologicalComplex` therefore constructs
the actual differentials and chain maps, including their square-zero and
commutation proofs.

`globalComplex` takes all global sections. `compactComplex` takes the full
submodule of sections whose local-vanishing support is compact.
`inclusionComplex` includes these submodules degree by degree. `globalHomology`
and `compactHomology` are the homology functors in the abelian category
`Rep R G`, and `inclusionHomology` is induced by the actual inclusion chain map.

`directImageComplex` applies full equivariant sheaf direct image in each
degree. `globalComplexIso` identifies its global sections with the original
global-section complex. For a proper spatial map, `properComplex` applies the
previously constructed compact-section transformation in each degree. Its
component formula, inclusion triangle, identity and spatial composition laws
are proved on the original sections. `properHomology` applies the homology
functor to this natural chain map. `globalHomologyIso` identifies the global
homology representations. The inclusion triangle, identity and spatial
composition equations also hold for these homology maps.

A supplied chain map `b : K → f_* F` gives `pullbackComplex`. Its degree `i`
component is exactly `ProperCompactSections.pullback` of `b.f i`; its
underlying-section formula is the original global component of `b.f i`.
Precomposition and postcomposition are natural in both complexes, and
spatial composition retains the supplied composite chain map.
`pullbackHomology` is homology of this constructed map. Its explicit
factorization through the direct-image compact homology, inclusion triangle,
identity, naturality and composition laws follow by functoriality from the
chain-map equations. The homology proofs apply the actual homology functor
to the proved chain-map equalities and use its identity and composition laws.

This is a derived internal consequence of the prior actual support and
direct-image constructions and Mathlib's homological algebra, rather than a
new claim from Harris or Berkovich. The complexes are genuine supplied input.
Identifying a particular resolution with derived compact cohomology requires
the corresponding resolution, acyclicity and comparison results. No such
comparison, preservation of smoothness, étale realization, arithmetic level
tower, or Harris specialization is asserted here.
