# Actual bundle extension when the base is a field

Worker 513 authored these internal inverse-pullback constructions for the
field-base case of `ValuationRingTwoAxisExtensionStatement`. This module
constructs actual line bundles and restriction isomorphisms. It does not
prove the extension assertion over a domain that is not a field.

For a scheme isomorphism `q : X ⟶ Y` and an actual line bundle `D` on `X`,
`LineBundle.extensionAlongIso q D` is the actual line bundle
`(LineBundle.pullback (inv q)).obj D` on `Y`. The line-bundle pullback
preserves the locally free rank-one property. Its restriction isomorphism,
`extensionAlongIsoRestrictionIso`, is the composite of the module-sheaf
pullback-composition comparison, the equality `q ≫ inv q = 𝟙 X`, and the
identity-pullback comparison. Thus it has type

```text
((LineBundle.pullback q).obj (extensionAlongIso q D)).obj ≅ D.obj.
```

`isIso_selfProductBaseChangeMap` applies Mathlib's isomorphism instance for
the induced map of pullbacks. If `b : T ⟶ S` is an isomorphism, both
base-change projections `X ×_S T ⟶ X` are isomorphisms. These projections
and `b` are the three components of the canonical self-product map
defined in the published `SelfProductBaseChange` module.

Now let `R : Type u` be a commutative domain with a proof `IsField R`,
and let `K : Type u` be any specified fraction field with its given
`Field K`, `Algebra R K` and `IsFractionRing R K` instances.
`isIso_fractionFieldSpecMap_of_isField` uses Mathlib's
`IsFractionRing.injective` and `IsFractionRing.surjective_iff_isField`
to show that this actual algebra map is bijective. It is therefore an
isomorphism in `CommRingCat`, and its image under the spectrum functor
is an isomorphism of schemes. No replacement algebra structure or
identification of `K` with a preferred fraction-field type is used.

`selfProductLineBundleExtension_of_isField` applies the preceding
constructions to every Library abelian scheme `A / Spec R` and every
line bundle `D` on the actual self-product of its actual base change to
`Spec K`. The extending bundle is inverse pullback along exactly
`mumfordProductBaseChangeMap A (Spec.map (CommRingCat.ofHom (algebraMap R K)))`.
This is the explicit canonical map `q` of the published host target.
The conclusion supplies an actual total-space line bundle `E` and
`Nonempty (q* E ≅ D)` on the underlying module sheaves.

There is no axis-triviality premise, valuation-ring instance, ampleness
assertion, or assumption about the characteristic. An arbitrary universe
`u` is retained. The field-base condition is essential to this argument:
it does not prove the host's arbitrary-rank valuation extension theorem
or the separate trait extension theorem. It also does not prove or
replace the separately owned field-ample result.

The provenance is internal. The only ingredients are the published
actual line-bundle pullback comparisons and self-product base-change
map, together with Mathlib's localization and categorical isomorphism
interfaces. No new mathematical source assertion, axiom, correspondence
representer, Picard comparison, or downstream valuative extension
theorem is used.
