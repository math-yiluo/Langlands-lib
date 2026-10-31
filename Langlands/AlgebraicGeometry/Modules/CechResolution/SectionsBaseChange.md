# Scalar sections maps on sheafified Čech complexes

## Scope and provenance

This internal construction works in an arbitrary universe `u`. Let
`φ : R ⟶ S` be a map of commutative rings, let `f : X ⟶ Spec R`,
`f' : Y ⟶ Spec S`, and `g : Y ⟶ X` satisfy
`g ≫ f = f' ≫ Spec.map φ`. Given actual module sheaves `M`, `N` and
`a : M ⟶ g_* N`, it constructs the maps on relative sections of the
sheafified Čech complex associated to an ordered affine cover of `X`.
The cover comparison requires `g` to be affine.

The file uses the specified maps from `CechResolution.BaseChange` and
`BaseChangeResolutionExactScalars`. Its conclusions are consequences of
those definitions, the scalar adjunction, finite biproduct preservation,
and their functoriality. It asserts no additional external geometric
result.

## Maps on an intersection factor

`factorSectionsMap` first applies `relativeGlobalSections f` to the
actual map `sheafOnPushforward g a hW`, where `hW : W' ≤ g ⁻¹ᵁ W`.
It then uses the canonical composition isomorphism for relative sections
and the inverse change-of-base-ring isomorphism. Its target is the
restriction along `φ` of the relative sections over `S`.

`scalarFactorSectionsMap` is the inverse hom-set equivalence of the
extension/restriction-of-scalars adjunction applied to this very map.
`scalarFactorSectionsMap_one_tmul` states that its value at `1 ⊗ x`
is `factorSectionsMap x`. The proof evaluates the inverse-equivalence
identity at `x` and uses Mathlib's evaluation formula for this adjunction.

## The specified cochain map and its projections

`scalarCechSectionsMap` is an abbreviation for the actual
`scalarResolutionSectionsBaseChangeMap` evaluated at
`cechPushforward g a 𝒰`. Its source is degreewise extension of scalars
of relative sections of `cechComplex 𝒰 M`, and its target is relative
sections of `cechComplex (inverseImageCover g 𝒰) N`.

`scalarCechSectionsMap_f_π` says that the degree-`p` map followed by
the target projection to the intersection indexed by `s` is the source
projection, after sections and scalar extension, followed by
`scalarFactorSectionsMap` for that intersection. To prove it, apply
injectivity of the scalar adjunction and its two naturality formulas.
The resulting ordinary sections square follows from naturality of the
composition and base-ring isomorphisms together with
`cechTermPushforward_π`. The implemented proof transports these
equalities explicitly by congruence and transitivity.

## Finite biproduct identifications

`sectionsBiproductIso` identifies relative sections of a finite
biproduct with the biproduct of the relative sections.
`scalarSectionsBiproductIso` does the same after extension of scalars.
Their indices may live in `Type u`, rather than only `Type 0`.
The local module-category biproduct instance is constructed from the
existing product using `HasBiproduct.of_hasProduct`.

Relative sections are a composite of right adjoints and preserve
products. Scalar extension is a left adjoint and preserves coproducts.
For the finite families in question these give preservation of
biproducts. Each displayed isomorphism is the uniqueness isomorphism
between the resulting limit cone and the already chosen biproduct
limit cone. The proof fixes the latter before installing preservation
instances, so the statement refers to its existing choice.
The two `hom_π` lemmas give precisely the mapped projections, by the
limit uniqueness isomorphism's projection identity.

`scalarCechSectionsMap_f_biproduct` expresses the actual degree map
as the biproduct of `scalarFactorSectionsMap`, through these source
and target isomorphisms. Projection extensionality, the preceding
projection formulas and `biproduct.map_π` prove this equality.

## Conditional invertibility

`isIso_scalarCechSectionsMap_f_of_factors` assumes invertibility of
every factor map in a specified degree. Their biproduct is invertible
by `biproduct.mapIso`; the preceding equality and cancellation of the
target biproduct isomorphism give invertibility of the actual degree map.

`isIso_scalarCechSectionsMap_of_factors` applies this argument in
every degree and uses `HomologicalComplex.Hom.isIso_of_components`.
`quasiIso_scalarCechSectionsMap_of_factors` then uses the standard
fact that an isomorphism of complexes is a quasi-isomorphism.

The factorwise hypotheses remain explicit. No flatness or
quasi-coherence hypothesis is needed for these conditional statements.
The file does not prove the factor maps invertible in a Cartesian
square, does not supply the acyclicity of the Čech terms or an
augmentation quasi-isomorphism, and does not prove localization
base change or the relative cube theorem. Those require further
geometric results.
