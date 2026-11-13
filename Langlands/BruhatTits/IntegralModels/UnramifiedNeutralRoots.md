# Actual root models inside the neutral component of a full fixer model

This internal construction proves that taking the relative identity
component preserves the actual root-group intersections of a supplied
smooth full fixer model. It constructs actual compatible integral maps,
as well as the resulting subgroup equalities.

Work first over a domain `R : Type u` with specified fraction field
`K : Type u`, and supplied `RelativeComponentModelData R K G`, denoted
`D`. A compatible map from an integral model `M` with geometrically
connected fibres to `D.full` factors through the represented relative
identity component. `factorConnectedModelHom` constructs this
factorization and verifies its generic commuting square using that of
`D.inclusion`. The factor composed with the component inclusion is the
original integral map. If that map is closed, the factor is closed,
because a closed immersion factoring through an open subscheme stays
closed in that subscheme.

For `A : IntegralSplitTorusData D.full i`, `factorNeutral` retains the
same integral split torus and generic identification, and factors its
integral inclusion through `D.neutral`. Its generic square still
commutes. A closed inclusion remains closed.

If the full model is smooth, the actual root models constructed in
`IntegralRootFiltration` have geometrically connected fibres. Thus
`rootModelNeutralMap` maps each of them into `D.neutral` with its
original generic root inclusion, and the new integral map is closed.
The exact full-model root-image identity then shows that
`rootGroupPoints i a ∩ D.full.integralPoints` lies in the neutral
integral points for every nonzero character `a`. The reverse inclusion
follows from the component inclusion. This proves
`rootGroupPoints_inf_neutral_eq_full`; no root-image equality for the
neutral model is supplied as an assumption.

Now use the actual maximal-unramified integers of a nonarchimedean
local field `F`, and `C : MaximalUnramified.BuildingData F G`. Suppose
the supplied full model has integral points
`characterValuationKernel (MaximalUnramified.valuation F) G ∩
C.pointwiseFixer (C.apartmentMap '' Ω)`.
The integral split apartment torus is constructed by
`UnramifiedIntegralRoots`. Its root intersection with the neutral
model is therefore exactly `C.apartment.rootFixer a Ω` for every
relative root `a`. Taking the join proves
`C.sharpFixer Ω ≤ D.neutral.integralPoints`. These two conclusions
hold for every apartment subset, without a nonemptiness or boundedness
assumption. For a nonempty subset bounded above under every real
affine functional, the existing root-fixer supremum formula gives the
exact level `C.apartment.rootFixerDepth a x Ω` at every reference point
`x`.

The provenance is internal: the proof composes actual connected-source
factorization, the constructed integral split torus and root models,
the full-fixer root-intersection theorem, and the bounded root-fixer
formula. It supplies the root part of the neutral comparison. It does
not identify a maximal torus Iwahori image, prove finite index or
congruence generation, or identify all neutral points with the
zero-subgroup fixer in `UnramifiedParahoricModelStatement`.
