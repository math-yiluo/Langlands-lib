# Actual exterior subsheaves of integral images

This internal module constructs an actual exterior subsheaf from integral
sections and proves that its image on every stalk is the exterior lattice
previously defined in `DeligneDeterminantLattice`. It supplies an independent
sheaf construction for the comparison with Deligne's determinant
condition in `DeligneDeterminantSubsheaf`. No original-literature theorem is
asserted in this module.

The parameters are a commutative ring O, an O-algebra field F, a space X,
an O-module sheaf M, an F-module sheaf N and an actual sheaf morphism
`f : M -> restriction N`. All rings, spaces and modules have the common
universe u. Every natural exterior degree n, including zero, is allowed.
There are no hypotheses of integral injectivity, finite generation, local
freeness or special topology.

## Construction from sections

`exteriorAmbient N n` is the scalar restriction to O of the actual
F-exterior sheaf of N. That exterior sheaf is the sheafification of the
sectionwise exterior-power presheaf, as constructed in
`ModuleExteriorStalk`.

For an open U and an n-tuple of M-sections, `exteriorSection` applies f
to the tuple, forms its actual F-exterior product, and applies the
exterior presheaf's sheafification unit. `exteriorSection_res` proves
that these sections commute with restrictions, using naturality of f
and of the sheafification unit and the formula for an exterior map.

`exteriorSectionSubmodule` takes the O-span of these exterior sections
on each open. Span induction and the restriction formula prove stability
under restriction. `exteriorSubsheaf` sheafifies this subpresheaf, using
`SectionSubmodule` from `ModuleSheafSubmodule`.
`exteriorSubsheafInclusion` is the resulting actual morphism into
`exteriorAmbient`; its monomorphism instance follows from that helper.
Thus the construction begins with sections and sheafification and does
not use any condition on stalk lattices to define the subsheaf.

## Actual stalk comparison

`restrictionStalkIso_germ` computes the scalar-restriction comparison
on any germ, directly from the colimit comparison identity.
`imageStalkMap` applies the actual O-module stalk functor to f and then
identifies the target with the scalar restriction of N's F-module stalk.
`imageStalkMap_germ` proves its section representative formula.

`exteriorAmbientStalkIso` combines the scalar-restriction comparison
with `exteriorSheafStalkIso`, identifying the ambient O-module stalk
with the scalar restriction of the F-exterior power of the actual N
stalk. Its germ formula is `exteriorAmbientStalkIso_germ`.
`exteriorSection_germ` consequently takes each sheafified exterior
section to the exterior product of its integral-image germs.

`exteriorSectionSubmodule_stalk_range` compares the stalk image of the
section subpresheaf, transported through this canonical ambient
isomorphism, with

```text
exteriorStalkLattice F n (stalk N x) (range (imageStalkMap M N f x)).
```

For the forward inclusion, membership in the subpresheaf's stalk image
has a single-neighborhood section witness. Span induction on that section
reduces to exterior generators, where `exteriorSection_germ` supplies
the required lattice generator. For the reverse inclusion, choose
preimages in the M stalk of the finitely many integral-image vectors.
`exists_fin_germs_eq` represents them simultaneously on one open
neighborhood; their exterior section supplies a stalk preimage of the
given generator. Span closure proves the full inclusion. This argument
also handles degree zero through the empty tuple.

`exteriorSubsheafStalkMap` is the actual generated subsheaf's stalk
inclusion followed by the ambient comparison.
`exteriorSubsheafStalkMap_range` proves that its linear range is exactly
the displayed exterior stalk lattice. It combines the preceding
comparison with the unchanged stalk-image theorem for sheafification
proved in `ModuleSheafSubmodule`.

The provenance is this explicit section construction and finite-neighborhood
argument. This module does not specialize both sides of the framed
determinant condition, compare equality of subsheaves on the Pi-zero loci,
or identify the full admissibility predicate with the original moduli
problem; `DeligneDeterminantSubsheaf` does the first two
(`determinantOnPiZeroLocus_eq_iff`). Those comparisons, formal-module
representability and level coverings remain separate.
