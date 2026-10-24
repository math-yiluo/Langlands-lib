# Scalar restriction in degree-zero étale cohomology

## Purpose and provenance

This internal construction transports the canonical ordinary-section scalar
comparison through the existing natural identification of degree-zero étale
cohomology with ordinary sections. It does so for actual small-étale module
sheaves, for their geometric group actions, and for compatible equivariant
coefficient diagrams over varying schemes.

The imported `EtaleScalarDiagram` and its dependencies supply the scalar
section comparisons and the degree-zero identifications. The latter come
from the actual right-derived global-section functor and its canonical
degree-zero isomorphism. No external literature theorem is transcribed,
and no scalar cohomology comparison is assumed.

## Parameters and conventions

The coefficient rings `R` and `A`, the scheme universe and module carriers
share universe `u`; `φ : R →+* A` is an arbitrary homomorphism of commutative
rings. No flatness or injectivity hypothesis is imposed. The group
`G : Type t` is algebraic, without topology, and acts through
`ρ : G →* (Aut X)ᵐᵒᵖ`. Thus the convention is
`aut(gh) = aut(g) ≫ aut(h)`.

For diagrams, `J` has objects in universe `v` and morphisms in universe `w`.
The functor `S : J ⥤ Scheme.{u}ᵒᵖ` sends `a : i ⟶ j` to an étale morphism
`X_j → X_i`. Actions `ρ i` and their compatibility `hρ` with these maps
are supplied. The coefficient objects are actual compatible equivariant
small-étale sheaves.

## Construction

Write `T_φ` for scalar restriction of coefficients, `r_φ` for scalar
restriction of modules (or of modules with group actions), and `Γ_R` for
ordinary sections over `R`. Let

```text
e_R : H⁰_R ≅ Γ_R,
σ_φ : Γ_R(T_φ -) ≅ r_φ(Γ_A -)
```

be the published canonical natural isomorphisms.
`scalarRestrictionCohomologyZeroIso` constructs

```text
H⁰_R(T_φ -) ≅ r_φ(H⁰_A -)
```

by the composite

```text
e_R(T_φ F) ≫ σ_φ(F) ≫ r_φ(e_A(F)⁻¹).
```

The Lean implementation uses whiskering of natural isomorphisms and their
composition, so naturality and inverse identities follow from the actual
three isomorphisms. `scalarRestrictionCohomologyZeroFunctorIso` applies
the same construction to the published geometric action functors and their
canonical section comparison. It is consequently an isomorphism in the
module-action category, with equivariant components.

`EquivariantCoefficientDiagram.restrictScalarsCohomologyZeroFunctorIso`
uses the same transport on functors whose values are `J`-diagrams of module
actions. Scalar restriction on such diagrams is postcomposition by `r_φ`,
implemented by `Functor.whiskeringRight`. This yields a comparison natural
in compatible coefficient diagrams, whose components commute with every
varying-scheme transition. The two `hom_app_app` and `inv_app_app` lemmas
identify its forward and inverse vertex maps with the preceding
single-scheme equivariant comparisons by reflexivity.

## Compatibility with ordinary sections

The three `..._sections` lemmas prove the commuting square

```text
κ_φ(F) ≫ r_φ(e_A(F)) = e_R(T_φ F) ≫ σ_φ(F),
```

where `κ_φ` denotes the constructed degree-zero comparison.
The first equality is in modules and the second in modules with group
actions. Their proofs expand the composite, use functoriality, and cancel
the adjacent inverse and forward components of `e_A`. The diagram equality
is an equality of natural transformations of module-action diagrams;
`NatTrans.ext` reduces it to the equivariant equality at every vertex.

These equations ensure that the degree-zero scalar comparison agrees with
the existing canonical section comparison under the existing degree-zero
identifications. The section comparison is not assumed to be an identity.

## Scope

Only degree zero is treated. This construction does not prove that scalar
restriction preserves injectives or commutes with positive-degree derived
cohomology. Identity/composition coherence for the degree-zero scalar
comparison, tensor extension, ideal reduction, inverse limits, smoothness,
analytic sites, compact supports and Harris specialization remain separate
obligations.
