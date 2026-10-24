# Scalar coherence for canonical section diagrams

## Purpose and provenance

This internal construction combines the published
`EtaleScalarDiagramCoherence` and `EtaleScalarSectionsCoherence` interfaces.
It constructs scalar identity and composition comparisons for diagrams of
modules with group actions and proves that the canonical ordinary-section
comparison of a varying-scheme equivariant coefficient diagram respects them.
No external literature theorem is transcribed. The provenance is the existing
scalar restriction functor, its canonical section comparison, and the proved
vertex compatibility equations in those modules.

## Parameters and conventions

The coefficient rings `R`, `A` and `B` are commutative rings in `Type u`.
The maps are arbitrary ring homomorphisms `φ : R →+* A` and `ψ : A →+* B`.
Module carriers have universe `u`. The index category has objects in
`Type v` and morphisms in `Type w`. The group `G : Type t` is algebraic;
no topology is supplied. No flatness, injectivity or surjectivity of the
ring maps is assumed.

The geometric part takes `S : J ⥤ Scheme.{u}ᵒᵖ`, so an arrow `a : i ⟶ j`
gives an étale morphism `X_j → X_i`, where `X_i = (S.obj i).unop`.
There is a supplied action `ρ i : G →* (Aut X_i)ᵐᵒᵖ` at each vertex,
and the supplied equality `hρ` says every transition commutes with these
actions. The opposite-automorphism convention is the existing one:
`aut(gh) = aut(g) ≫ aut(h)`. Coefficient diagrams contain actual
small-étale module sheaves with compatible equivariant transition maps.

## Scalar restriction of module-action diagrams

Write `r_φ` for scalar restriction on modules with `G`-action, and
`P_φ` for postcomposition by `r_φ` on `J`-diagrams.
`actionDiagramRestrictScalarsFunctor` is precisely that postcomposition
functor, using `Functor.whiskeringRight`. It changes the scalar action
along `φ` at every vertex and restricts each transition and each component
of a natural transformation.

`actionDiagramRestrictScalarsIdIso` constructs a natural isomorphism

```text
P_id_R ≅ Id
```

whose component at `V : J ⥤ Action (ModuleCat R) G`, evaluated at `i`,
is the existing `actionRestrictScalarsIdIso` at `V.obj i`.
`actionDiagramRestrictScalarsCompIso` constructs

```text
P_(ψ.comp φ) ≅ P_ψ ⋙ P_φ.
```

Its component is the existing `actionRestrictScalarsCompIso φ ψ G`
at each `V.obj i`. Thus direct restriction along `R → B` is compared
to restriction first along `A → B` and then along `R → A`.

Both constructions use `NatIso.ofComponents` twice. The inner naturality
proof uses naturality of the module-action comparison for `V.map a`,
so it verifies every diagram transition. The outer naturality proof
uses the same equation for each component `α.app i` of a morphism of
diagrams. The inverse identities are inherited by `NatIso.ofComponents`
from the actual isomorphisms. The four `hom_app_app` and `inv_app_app`
lemmas expose these forward and inverse vertex maps by reflexivity.

## Canonical section compatibility

Write `T_φ` for scalar restriction of equivariant coefficient diagrams,
`Γ` for their ordinary-section action diagram functor, `η_D` for the
coefficient identity comparison, and `μ_(φ,ψ),D` for its composition
comparison. Write `σ_φ,D` for the existing canonical diagram isomorphism

```text
Γ(T_φ D) ≅ P_φ(Γ D).
```

This is `restrictScalarsSectionsIso` from `EtaleScalarDiagram`. Its
components are the canonical single-scheme section comparisons constructed
using the isomorphism from ordinary global sections to terminal evaluation.
The present file reuses those components; it does not replace them by
identity maps.

For an `R`-coefficient diagram, `restrictScalarsSections_id` proves

```text
Γ(η_D) = σ_id_R,D ≫ ε_(Γ D),
```

where `ε` is the new identity comparison on module-action diagrams.
Both sides are maps from `Γ(T_id_R D)` to `Γ D`.

For a `B`-coefficient diagram, `restrictScalarsSections_comp` proves

```text
Γ(μ_(φ,ψ),D) ≫ σ_φ,(T_ψ D) ≫ P_φ(σ_ψ,D)
  = σ_(ψ.comp φ),D ≫ ν_(φ,ψ),(Γ D),
```

where `ν` is the new composition comparison on module-action diagrams.
Both sides go from `Γ(T_(ψ.comp φ) D)` to `P_φ(P_ψ(Γ D))`.

These are equalities of natural transformations of `J`-diagrams in the
module-action category, so all components are equivariant and compatible
with the varying-scheme transitions. The proofs use `NatTrans.ext` to
reduce the equalities to the published
`scalarRestrictionSectionsFunctor_id` and
`scalarRestrictionSectionsFunctor_comp` at `D.obj i`. The inherited
definitions of section maps and scalar comparisons give exactly these
vertex equations. No additional compatibility hypothesis is assumed.

## Scope

This unit treats ordinary global-section action diagrams and scalar
identity/composition compatibility. It does not construct a positive-degree
derived scalar comparison, preservation of injectives, tensor extension,
ideal reduction, inverse limits, smoothness, analytic sites, compact
supports or a Harris-specific tower. Those remain separate obligations.
