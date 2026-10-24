# Identity and composition for equivariant scalar restriction

This module constructs identity and composition isomorphisms for scalar
restriction on actual small-etale module sheaves and on geometric equivariant
sheaves. It identifies their sectionwise maps and proves the two unit laws and
the associativity law for three ring homomorphisms in both categories.

## Provenance and parameters

This is an internal construction from the published `EtaleScalarRestriction`
module and Mathlib's `ModuleCat.restrictScalarsId` and
`ModuleCat.restrictScalarsComp`, defined in
`Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.lean`. No external theorem is
transcribed. The module comparisons preserve the underlying elements while
identifying the relevant scalar actions. Postcomposing each sheaf's presheaf
with these comparisons gives the sheaf comparisons. Their sectionwise formulas
also give the equivariance and coherence proofs; none of the desired comparison
maps or laws is supplied as a hypothesis.

The coefficient rings `R, A, B, C : Type u` are commutative rings. The ring maps
are arbitrary:

```text
φ : R →+* A,    ψ : A →+* B,    χ : B →+* C.
```

The scheme is `X : Scheme.{u}`, and section-module carriers also use universe
`u`. The sheaf category is `EtaleDerivedSections.ModuleSheaf X R`, namely
`Sheaf X.smallEtaleTopology (ModuleCat.{u} R)`, with the analogous categories
for the other rings. There is no injectivity, surjectivity or flatness assumption
on the ring maps.

For equivariant coefficients, `G : Type t` is a group and
`ρ : G →* (Aut X)ᵐᵒᵖ` is supplied. There is no required topology on `G`.
The opposite automorphism convention is the existing one:
`aut ρ (g * h)` is `aut ρ g` followed by `aut ρ h`. An
`EquivariantSheaf R ρ` has an actual small-etale sheaf and geometric translation
structure maps satisfying the unit and multiplication laws.

## Comparisons on sheaves

`sheafRestrictScalarsIdIso X` constructs the natural isomorphism

```text
sheafRestrictScalars (RingHom.id R) X ≅ identity.
```

At a sheaf `F`, its forward and inverse maps are obtained by precomposing the
corresponding natural transformations of `ModuleCat.restrictScalarsId R`
with `F.obj`. Thus at `U : X.Etaleᵒᵖ` they are exactly the module comparisons
on `F.obj.obj U`. The lemmas `sheafRestrictScalarsIdIso_hom_app` and
`sheafRestrictScalarsIdIso_inv_app` record these formulas.

`sheafRestrictScalarsCompIso φ ψ X` constructs

```text
sheafRestrictScalars (ψ.comp φ) X
  ≅ sheafRestrictScalars ψ X ⋙ sheafRestrictScalars φ X.
```

The source category has `B` coefficients and the target has `R` coefficients.
Its components are similarly obtained from `ModuleCat.restrictScalarsComp φ ψ`;
`sheafRestrictScalarsCompIso_hom_app` and
`sheafRestrictScalarsCompIso_inv_app` identify the forward and inverse maps
on each section module. They preserve the underlying elements. The scalar
operations agree because restricting successively makes `r` act as
`ψ (φ r)`. Inverse identities and naturality in coefficient sheaf morphisms
are proved by sheaf, natural-transformation and module-map extensionality.

The three sheaf coherence lemmas describe maps at every coefficient sheaf:

- `sheafRestrictScalarsCompIso_id_left` splits the map
  `φ.comp (RingHom.id R)` into successive restrictions, then removes the
  identity restriction on the resulting `R`-sheaf. This composite is identity.
- `sheafRestrictScalarsCompIso_id_right` splits
  `(RingHom.id A).comp φ`, then applies scalar restriction along `φ` to the
  identity comparison on the original `A`-sheaf. This is also identity.
- `sheafRestrictScalarsCompIso_assoc` compares the two ways of splitting the
  triple composite into restriction first along `χ`, then `ψ`, then `φ`.
  One first splits off `φ` and then splits `χ.comp ψ` inside scalar restriction
  along `φ`. The other first splits off `χ` and then splits `ψ.comp φ` on the
  already `χ`-restricted sheaf. The resulting maps agree.

The identity and associative ring composites in these formulas have
definitionally matching source and target sheaf data. Each proof evaluates the
maps at a section element, where both sides return that element.

## Comparisons with geometric equivariance

`scalarRestrictionIdIso ρ` and `scalarRestrictionCompIso φ ψ ρ` construct

```text
scalarRestrictionFunctor (RingHom.id R) ρ ≅ identity,

scalarRestrictionFunctor (ψ.comp φ) ρ
  ≅ scalarRestrictionFunctor ψ ρ ⋙ scalarRestrictionFunctor φ ρ.
```

Their underlying sheaf isomorphisms are exactly the preceding sheaf
comparisons. `TranslationAction.Equivariant.mkIso` lifts them once equivariance
of their forward maps is proved. For every group element, evaluation on a
section identifies both sides of the equivariance equation with the original
structure map on the same element. The constructor derives equivariance of
the inverse. Naturality follows by forgetting equivariance and evaluating on
sections.

`scalarRestrictionIdIso_hom_app_hom`,
`scalarRestrictionIdIso_inv_app_hom`,
`scalarRestrictionCompIso_hom_app_hom`, and
`scalarRestrictionCompIso_inv_app_hom` identify both underlying sheaf maps of
the two comparisons. The equivariant coherence lemmas
`scalarRestrictionCompIso_id_left`, `scalarRestrictionCompIso_id_right`, and
`scalarRestrictionCompIso_assoc` have the same two unit formulas and triple
composition formula as above, now as equalities of equivariant morphisms.
Their proofs use extensionality of equivariant morphisms and the corresponding
sheaf coherence lemma.

## Scope

This unit treats scalar restriction on ordinary small-etale sheaves and its
compatibility with the supplied geometric group action. It does not lift these
identity/composition comparisons to compatible coefficient diagrams or prove
compatibility with the canonical global-section scalar comparison. It makes no
higher-derived scalar comparison, injective-preservation, tensor-extension,
ideal-reduction, inverse-limit, smoothness, analytic-site, compact-support or
Harris-specialization claim. Those constructions retain their separate
obligations in the broader framework.
