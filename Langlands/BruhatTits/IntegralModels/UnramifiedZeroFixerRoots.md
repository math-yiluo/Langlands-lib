# Actual integral tori and root models of unramified zero fixers

This internal construction works at arbitrary universe `u`. Let `F` be a
nonarchimedean local field, `C` an actual maximal-unramified building datum for
an affine group `G` over its inertia fixed field, and `E` any unramified zero
datum for `G`. The torus used by `E` need not agree with the apartment torus
of `C`. Let `N` be an actual affine flat integral model over the inertia-fixed
integers. Assume its integral points equal the intersection of `E.zeroPoints`
with the pointwise fixer of the apartment image of a set `Ω`.

`unramifiedZeroFixerIntegralSplitTorusData` constructs an actual integral split
torus mapped into `N`, together with its generic identification with the
apartment torus and the commuting generic inclusion square. The inclusion
is a closed subgroup. No smoothness of `N`, nonemptiness of `Ω`, or boundedness
of `Ω` is required for this construction.

The proof first includes the bounded apartment-torus points in the supplied
zero fixer. The published result
`UnramifiedZeroDatum.map_split_characterValuationKernel_le_zeroPoints`
puts them in the zero subgroup for every datum; the apartment action of torus
units puts them in the pointwise fixer. The fixed-field integers are a discrete
valuation ring with algebraically closed, hence infinite, residue field, and
all their units have normalized valuation one. The existing closed split-torus
construction from bounded points therefore supplies the claimed torus, map,
and generic identification.

Assume now that `N` is smooth. The published `IntegralSplitTorusData` root
construction applies to the chosen torus. Its generic inclusion represents
the full relative-root subgroup on every scheme test, and its integral map
is a closed subgroup inclusion. The theorem
`unramifiedZeroFixerRootModel_integralPoints_eq` proves that the integral
point image of this actual root model is exactly `C.apartment.rootFixer a Ω`.
Indeed, the closed-root-model integral-point theorem computes the image as
the intersection of `N.integralPoints` and the actual root-group points.
Substitution of the zero-fixer characterization and the published
`rootGroupPoints_inf_unramifiedZeroFixer_eq_rootFixer` gives the result. This
identity requires neither nonemptiness nor boundedness of `Ω`.

For nonempty `Ω` bounded above under every real affine functional,
`unramifiedZeroFixerRootFiltrationModelData` packages these actual root models
at the existing depth `C.apartment.rootFixerDepth a x Ω`, for any reference
point `x`. The published bounded root-fixer calculation identifies the fixer
with that filtration level. Smoothness, affineness, and geometrically connected
fibres come from the integral full-root construction. The accompanying
`unramifiedZeroFixerRootFiltrationModelMap` is its actual compatible closed
integral inclusion into `N`.

The construction uses no supplied integral-torus, root-model, or root-image
predicate and no full one-fixer model. It is derived from the existing
bounded-torus closure, full-root model, and zero-fixer intersection results.
It supplies integral models needed for comparing incident facets. It does
not identify their residue images with residue-root subgroups or establish
the host facet-to-parabolic bijection.
