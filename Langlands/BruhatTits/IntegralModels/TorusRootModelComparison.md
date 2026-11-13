# Compatible comparisons of supplied torus/root model families

This internal unit assembles comparison maps for two supplied
`TorusRootModelFamilyData` over the maximal unramified integers of the same
local field. Both families use the same building data, zero datum and reference
point, while their subsets and ambient models may differ. It assumes the
explicit `IntegralModel.HasSmoothHomExtension` criterion and constructs no
families, open cells or special-fibre kernel geometry.

`torusComparisonIso` gives an actual integral-model isomorphism from the second
family's torus model to the first. Their integral-point images are both exactly
the same zero datum's torus Iwahori subgroup. The published
`isoOfIntegralPointsEq` construction applies the extension criterion in both
directions and generic rigidity proves the inverse identities. Its generic map
is the identity of the original torus.

`genericComparisonIso` uses that torus identity at the index `none`, and at
`some a` uses the canonical generic isomorphism between the two actual
representatives of root `a`. `genericComparisonIso_hom_comp` proves
compatibility with all the generic inclusions into the ambient group.

`comparisonHom` takes the inequality between the two root-fixer depths for
every relative root. At `none` it uses the torus isomorphism; at `some a` it
uses the root-model comparison from `RootFiltrationModelComparison`. Each map
is from the second family's actual model to the first family's actual model.
The common index is `Option (relativeRoots C.i)`; no enumeration, ordering or
product decomposition is asserted.

`comparisonHom_comp` proves that every integral comparison commutes with the
two supplied ambient model maps and any ambient comparison extending the
generic identity. The root case reuses the root comparison square; the torus
case follows from generic rigidity and the torus isomorphism's compatibility.
`comparisonHom_specialFibre_comp` base changes those exact squares along the
actual residue quotient. `torusSpecialFibreComparisonIso` base changes the
actual torus-model isomorphism, and its homomorphism is definitionally the
`none` factor's special-fibre comparison.

`rootDepth_le_of_subset_affineClosure` supplies the depth inequalities from a
nonempty first subset contained in the initial affine closure of a second
subset whose image under every real affine functional is bounded above.
It applies the closure-depth comparison to each negative affine root
functional. The hypotheses use the literal initial topology in the host
target. `comparisonHomOfClosure` applies these inequalities to construct every
family map; `comparisonHomOfClosure_comp` supplies its ambient squares.

All assertions are derived from the supplied model data and published
representability, filtration, extension-interface and generic-rigidity
constructions. The extension criterion remains an input rather than a proved
arithmetic theorem. This unit supplies compatible factor maps for the host
kernel argument; it does not establish that argument's remaining existence,
containment or root-kernel obligations.
