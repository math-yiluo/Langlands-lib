# Local-vanishing and stalk compact-section complexes

This internal construction compares the actual compact-section complexes from
`ProperCompactComplexes` with the stalk-support complexes in
`EquivariantSections`. The space, commutative ring and coefficient-module
universes are aligned to `u`, as required by the existing stalk construction.
The group universe `v` and the arbitrary complex-index universe `t` are
independent. Individual group translations are continuous.

`compactComplexIso` applies Mathlib's `NatIso.mapHomologicalComplex` to the
proved local-vanishing/stalk support comparison. Its forward and inverse maps
preserve the original section in every degree. Both global-section complexes
are definitionally identical; `globalComplexIso` records their identity.
The comparison commutes with the support-forgetting chain inclusions.
Applying the homology functor in `Rep R G` gives `compactHomologyIso` and
`globalHomologyIso`, with the corresponding inclusion triangle.

For a continuous equivariant proper map, `properComplex` transports the
constructed proper local-compact chain map through these actual chain
isomorphisms. Its underlying-section formula, comparison square,
support-forgetting triangle, identity and spatial composition laws follow
by equality on the original sections. `properHomology` is induced by this
chain map; it satisfies the corresponding support comparison, inclusion,
identity and composition laws.

A supplied genuine chain map `b : K → f_* F` gives `pullbackComplex`
between the existing stalk compact-section complexes. In every degree its
underlying section is the image under the original global component of
`b.f i`. It commutes with the local/stalk comparison and support-forgetting
inclusions. The identity, precomposition, postcomposition and spatial
composition equations hold for these actual maps. `pullbackHomology` is
homology of this constructed chain map. Its factorization through compact
homology of the full direct image, comparison square, inclusion triangle and
all corresponding functoriality equations are proved by applying the
homology functor to the chain-map equalities.

The provenance is the existing proved equality of local and stalk support,
the genuine proper local-compact pullback construction, and Mathlib's
functorial homological algebra. No choice of a resolution is included.
Derived compact-cohomology comparisons, resolution acyclicity, spatial maps
of Godement resolutions, smoothness preservation, étale realization and the
Harris specialization remain separate obligations.

No topology on the group or coefficients, separation, local compactness,
boundedness or finite dimensionality is assumed. The construction takes all
compact sections in the algebraic representation category, without asserting
that they are smooth.
