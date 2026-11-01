# Canonical pullback on actual relative cohomology

This construction implements the f-map route of the Stacks Project,
`cohomology.tex`, section *Functoriality of cohomology*, tags 01F7–01FB,
at commit `a04446e57ec1fbc252a871afcec7752fb2807b14`. The registered source is
`stacks-flasque-affine-vanishing-kunneth-a04446e5`.
Its internal comparison infrastructure is the actual acyclic-term derived-unit
theorem `Langlands.Cohomology.acyclicTermsDerivedUnitStatement`, together with
the existing comparison between bounded-below and classical right derived
functors in `DerivedPlus`. The elementary section comparisons and the general
acyclic-term comparison were developed in coordination with Worker 595.

For a morphism `h : Y ⟶ X` over `Spec R` and an actual module `M` on `X`,
put `N = h^* M` and let `I` be Mathlib's chosen injective resolution of `N`.
`pullbackResolutionAugmentation` forms the actual adjunction unit
`M ⟶ h_* N`, followed by `h_*` of the augmentation `N ⟶ I`.
It first does this for natural-indexed complexes using the published
`AcyclicResolution.mapAugmentation`, then extends by zero to integer-indexed
complexes, using `DerivedPlus.mapExtendIso` to compare extension with
termwise pushforward.

`pullbackDerivedAugmentation` applies the localization functor to this map
and transports through the canonical single-object and bounded-below
inclusion comparisons. Its target is represented by the entire complex
`h_* I`, including possible nonzero higher-direct-image homology.
`pullbackSectionsComplexIso` applies
`relativePushforwardSectionsIso h` termwise to identify the complex
`Γ_X(h_* I)` with `Γ_Y(I)`.

`relativeDerivedSectionsPullback` applies the actual bounded-below right
derived sections functor on `X` to the derived augmentation. Every term of
`h_* I` is sections-acyclic by the published
`pushforwardInjectiveAcyclic`. The acyclic-term derived-unit theorem therefore
makes the actual component
`(relativeGlobalSections X.hom).rightDerivedFunctorPlusUnit.app (h_* I)`
invertible. Composing with its inverse reaches the derived-category image
of `Γ_X(h_* I)`, then the termwise sections comparison reaches `Γ_Y(I)`.
Finally the inverse of `DerivedPlus.derivedComplexIso` reaches the actual
derived sections of `N` on `Y`. This realizes the inverse vertical arrow
in Stacks tag 01FB without an acyclicity assumption on `N` or on `h_* N`.

`relativeCohomologyPullback h M n` takes degree-`n` homology of that derived
map. On each side it uses the published `DerivedPlus.homologyIso` to identify
this homology with the actual classical right derived functor
`DerivedSections.relativeCohomology`. The coefficient object is Mathlib's
actual `Scheme.Modules.pullback h.left` applied to `M`. All constructions
use an arbitrary universe, an arbitrary commutative base ring, arbitrary
scheme morphisms over that base and arbitrary structure-sheaf modules,
including degree zero. No caller-supplied map, vanishing certificate or
geometric premise occurs.

The underlying `DerivedSections` definitions and their import closure are
unchanged. The elementary section map and split coefficient isomorphism
come from `CohomologyPullbackSections`. This construction asserts no identity,
composition, coefficient naturality, degree-zero compatibility or
split-retraction law; those are separate later statements and proofs.
