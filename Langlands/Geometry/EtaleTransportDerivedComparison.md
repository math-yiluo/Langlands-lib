# Ordinary cohomology underlying derived transport sections

Author: Worker 13.

This internal construction compares actual derived sections of module sheaves
on the group-labelled small-etale transport site with ordinary small-etale
derived sections. The scheme is `Y : Scheme.{u}`; the group `G : Type w`
has an independent universe and an explicit `Small.{u} G` assumption.
The action is the established homomorphism
`ρ : G →* (Aut Y)ᵐᵒᵖ`. The commutative ring `R` and all module and
representation carriers lie in `Type u`. Representations are algebraic.

Write `S = sectionRepresentation ρ R`, `U = forget₂ (Rep R G) (ModuleCat R)`,
`T = toSheaf ρ (ModuleCat R)` and `Γ = EtaleDerivedSections.sections Y R`.
These are constructed functors on actual sheaf and representation categories.
The previously constructed natural isomorphism `τ : S ⋙ U ≅ T ⋙ Γ`
compares their section functors. `EtaleTransportInduction` proves that `T`
is exact and preserves injective objects. No derived comparison is an input.

`ordinaryResolution` sends every injective resolution `I` of a transport
sheaf `F` to the termwise `T`-image resolution of `T(F)`. Exactness makes its
augmentation a quasi-isomorphism, and preservation of injectives supplies
the resolution's injective terms. `ordinaryResolution_ι_f_zero` states that
its degree-zero augmentation is precisely `T.map (I.ι.f 0)`.

`resolutionComplexIso` is the strict natural-indexed complex isomorphism
between `U` applied termwise to the section representation complex of `I`
and ordinary sections of `ordinaryResolution I`. It is the complex map
induced by `τ`. `cohomologyForgetIso q` is the natural isomorphism

`DerivedSections.cohomology ρ R q ⋙ U ≅ T ⋙ EtaleDerivedSections.cohomology Y R q`

for each `q : ℕ`. It uses exactness of `U`, exactness and injective
preservation of `T`, and the section comparison. Its source is the right
derived functor computed in the transport-sheaf category; its target is
ordinary small-etale cohomology of the restricted sheaf.

The bounded-below constructions explicitly allow independent Mathlib
`HasDerivedCategory` localization choices for transport sheaves, ordinary
sheaves, representations and modules. These assumptions concern the
existence of the categorical localizations and have Mathlib's standard
realizations. Only constructions involving derived representations use the
representation localization.

`moduleDerivedSections` derives `S ⋙ U` in the transport-sheaf source
category, with values in `DerivedCategory.Plus (ModuleCat R)`. This is the
actual right derived functor applied to a sheaf placed in degree zero.
`ordinaryDerivedMap` applies the existing exact-source construction
`DerivedPlusSource.derivedMap` to `T` and `τ.hom`. It therefore defines a
natural transformation to `T ⋙ EtaleDerivedSectionsPlus.derivedSections Y R`.

To construct `ordinaryDerivedIso`, the implementation proves that the square
on each injective resolution is an isomorphism: before extension by zero it
is a component of `NatIso.mapHomologicalComplex τ`; extension preserves
isomorphisms, and the fully faithful bounded-below-complex inclusion
reflects them. Localization preserves this isomorphism. Composing it with
the actual resolution comparison isomorphisms proves that every component
of `ordinaryDerivedMap` is invertible. Pointwise invertibility then gives
the natural isomorphism. No equivalence between actions on derived objects
and derived representation objects is assumed.

`ordinaryDerivedIso_hom_app` computes the comparison with every transport
injective resolution, using its restricted ordinary resolution. In the
notation of `DerivedPlusSource`, its forward map is
`imageResolutionIso(S ⋙ U,I).hom`, followed by the localization of the
extended square induced by `τ`, followed by
`imageResolutionIso(Γ,T(I)).inv`. This formula is independent of the
chosen resolution through the imported exact-source construction.
`ordinaryDerivedIso_homology` states that the nonnegative homology of this
map is exactly the homology map of that resolution square, conjugated by
the standard derived and resolution-cohomology comparisons.
`moduleHomologyNatIso q` consequently identifies homology of
`moduleDerivedSections` naturally with ordinary etale cohomology of `T(F)`.

`derivedForgetIso` compares the actual derived representation-valued
section functor with ordinary derived sections after inclusion into the
unbounded derived category of modules. Its source first includes the
bounded-below derived representation object in the unbounded derived
category of representations and then applies `U.mapDerivedCategory`.
It composes `DerivedPlus.derivedPostcompIso S U`, justified by exactness
of the representation forgetful functor, with `ordinaryDerivedIso`
whiskered by the bounded-below inclusion. The target is ordinary derived
sections of `T(F)`, included into the unbounded derived category of modules.
`diagramOrdinaryIso` whiskers the bounded-below module comparison by any
coefficient diagram, with independent indexing object and morphism
universes. It takes no inverse limit.

The provenance is internal categorical assembly. The module specializes
`DerivedComparison.mapInjectiveResolution`, `complexIso` and
`rightDerivedCompIso`, `DerivedPlusSource`'s exact-source resolution
comparison, and `DerivedExactPostcomposition`'s exact-target comparison.
The geometric inputs are the actual transport sections, exact restriction
and injective resolutions from the imported transport modules, together
with the ordinary constructions in `EtaleDerivedSectionsPlus`. These
generic constructions and Mathlib's extension, localization and natural
isomorphism operations supply all intrinsic obligations. No new theorem
is attributed to Harris or Berkovich.

The construction concerns sheaves inserted in degree zero and ordinary
global sections. Smoothness for topological groups, compact supports,
analytic uniformization, arithmetic coefficient systems, level towers
and the required Harris specialization remain separate obligations.
No smooth action or comparison for these further constructions is claimed.
