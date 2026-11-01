# Localization and coefficient maps of actual locally constant sections

Author: Worker 56.

Fix an actual indexed affinoid atlas `a` on `X` over a complete ultrametric
normed field. The field, point, chart-index and coefficient universes are
independent. This module uses the constructed original-chart domain
category and its actual quasinet site. All coefficient types are arbitrary:
they have no topology, algebra, action or nonemptiness assumption.

## Coefficient maps

`locallyConstantCoefficientMap` postcomposes every locally constant
section with an arbitrary coefficient function. Evaluation gives exactly
`φ (f x)`. Literal inclusion pullbacks commute with this operation
pointwise, proving its naturality. `locallyConstantSheafMap` bundles the
same natural transformation between the constructed sheaves.
`locallyConstantSheafFunctor a` sends each type in the arbitrary coefficient
universe to its actual section sheaf; identity and composition follow by
evaluating sections at points. Its target is the sheaf category with
values in `Type (max v z)`, where `v` is the point universe and `z` is the
independent coefficient universe.

`locallyConstantSieveGlue_map` proves that this operation commutes with
the previously constructed gluing for every arbitrary covering sieve.
At each target point, point coverage supplies a sieve domain containing
it. Both constructed glues evaluate there to the corresponding local
section, and postcomposition gives the same coefficient value.
The new family is Mathlib's actual `FamilyOfElements.map`; its full
compatibility follows from naturality of the coefficient transformation.

## Localization of sections and sheaves

Let `S` be an original-chart domain of `a`, and let `U` be a domain of
the constructed subspace atlas on `S`. The published `subspaceExtend U`
is the actual ambient image `Subtype.val '' U.carrier`.
`OriginalDomainNested` constructs the homeomorphism
`S.subspaceExtendHomeomorph U` from that ambient image to the nested
subtype. Its maps insert and forget the intermediate membership in `S`;
it uses the actual induced topologies.

`locallyConstantLocalizationEquiv S U` applies Mathlib's
`LocallyConstant.congrLeft` to this homeomorphism. Its forward map
forgets the intermediate membership before evaluating the given
ambient-image function. Its inverse inserts that membership before
evaluating the nested function. The two `apply` lemmas display these
original point maps explicitly. The two restriction lemmas prove
commutation with literal subset inclusions in both directions:
the functions agree by evaluation, and membership proofs are irrelevant.

`locallyConstantLocalizedPresheaf S A` has all locally constant functions
on each ambient image as its sections and literal ambient inclusion
pullbacks as its restrictions. `locallyConstantLocalizedPresheaf_eq`
identifies this presentation with the ambient presheaf pulled back along
`S.subspaceExtensionFunctor.op`, by definitional equality.

`locallyConstantLocalization S A` packages these equivalences as a
natural isomorphism from the ambient presheaf pulled back along
`S.subspaceExtensionFunctor.op` to the actual locally constant presheaf
of the subspace atlas. The restriction equality proves naturality.
`locallyConstantLocalization_isSheaf` transports the proved arbitrary
covering-sieve sheaf condition through this explicit isomorphism.
`locallyConstantLocalizedSheaf` bundles the literal ambient-image
presheaf and that proof on the unchanged subspace site.
`locallyConstantSheafLocalization` gives an isomorphism of these actual
sheaves; its underlying maps are precisely the preceding function maps.

`locallyConstantLocalization_coefficient_naturality` proves equality of
the two natural transformations obtained by localizing and changing
coefficients in either order. Evaluation reduces both to applying the
same coefficient function to the same ambient point value.

## Constructed gluing under localization

For an arbitrary covering sieve on a subspace domain, take a fully
compatible family in the ambient-image presheaf. The input sections are
actual functions on the ambient images, with the actual ambient
inclusions as restrictions. `locallyConstantLocalizationSieveGlue` maps
the family to nested sections using the constructed natural
transformation, applies the existing arbitrary-sieve locally constant
gluing construction, and transports the result back through the inverse
function equivalence.

`locallyConstantLocalizationSieveGlue_apply` proves that this function
recovers every original ambient-image section along its literal ambient
subset inclusion. It evaluates the nested gluing law at the nested
point corresponding to the given ambient point.
`locallyConstantLocalizationSieveGlue_localize` proves equality with
the constructed nested glue after localization, by the function
equivalence's inverse law. `locallyConstantLocalizationSieveGlue_unique`
proves uniqueness directly: point coverage on the nested subspace
supplies a sieve domain containing the corresponding point, and any
amalgamation has the original local value there. It must therefore equal
the constructed ambient-image function at every point.

## Provenance and scope

This is an internal construction from `OriginalDomainLocalization`,
`OriginalDomainNested`, `OriginalDomainLocallyConstantSheaf`, Mathlib's
locally constant function equivalences and the full sheaf subcategory.
Its provenance is the explicit nested-subspace homeomorphism,
precomposition and postcomposition, pointwise restriction equations,
constructed covering-sieve glue and uniqueness arguments above.
There is no separately attributed original-source assertion.

Empty domains, permitted empty covering sieves and empty coefficient
types remain allowed; the proofs choose local values only at actual
points where point coverage supplies them. The result concerns these
concrete constant-coefficient function sheaves on the existing
fixed-original-chart domain sites. General sheaf-category localization,
identification with a categorical constant-sheaf functor, full analytic
or etale sites and the Harris tower are separate constructions.
