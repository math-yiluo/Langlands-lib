# Identity and composition for scalar extension of coefficient diagrams

`Langlands.Geometry.EtaleScalarExtensionDiagramCoherence` constructs canonical
identity and composition isomorphisms for scalar extension on compatible
equivariant small-etale coefficient diagrams. All declarations lie in
`Langlands.Geometry.EtaleCohomologyAction.EquivariantCoefficientDiagram`.

## Parameters and provenance

The commutative rings `R A B C : Type u` are arbitrary, with unital ring maps
`φ : R →+* A`, `ψ : A →+* B`, and `χ : B →+* C`. Schemes and module carriers
also use universe `u`. The indexing category `J` has object universe `v` and
morphism universe `w`. Supply `S : J ⥤ Scheme.{u}ᵒᵖ`, all its geometric maps
`(S.map a).unop` etale, and a fixed abstract group `G : Type t`. The actions
`ρ i : G →* (Aut (S.obj i).unop)ᵐᵒᵖ` satisfy the supplied equations

```text
(S.map a).unop ; (aut (ρ i) g).hom =
  (aut (ρ j) g).hom ; (S.map a).unop,       a : i ⟶ j.
```

Here `;` denotes composition in order of application. Coefficient transitions
need not be invertible. The extension functors use the actual sectionwise
tensor construction followed by sheafification at each vertex.

This is an internal categorical construction. It imports the
[diagram adjunction](EtaleScalarDiagramAdjunction.md),
[diagram restriction comparisons](EtaleScalarDiagramCoherence.md), and
[pointwise equivariant extension comparisons](EtaleEquivariantScalarExtensionCoherence.md).
Mathlib's `conjugateIsoEquiv` transfers the inverse restriction comparisons
through the actual adjunctions. The pointwise formulas and coherence laws
are proved below; none is supplied as a field or hypothesis. No external
literature theorem is transcribed in this unit.

## Canonical comparisons

Write `L_φ` for `extendScalarsFunctor φ`, `U_φ` for
`restrictScalarsFunctor φ`, and `η_φ(D)` for `extensionUnitApp φ D`.
The new natural isomorphisms are

```text
extendScalarsIdIso       : L_id ≅ identity,
extendScalarsCompIso φ ψ : L_(ψ ∘ φ) ≅ L_φ ⋙ L_ψ.
```

`extendScalarsIdIso` is the inverse conjugate of
`restrictScalarsIdIso.symm` using the identity adjunction and the extension
adjunction for the identity ring map. `extendScalarsCompIso` is the inverse
conjugate of `(restrictScalarsCompIso φ ψ).symm` using the composite
adjunction `(extensionRestrictionAdj φ).comp (extensionRestrictionAdj ψ)`
and the adjunction for `ψ.comp φ`.

Consequently these are isomorphisms of the actual compatible diagram
categories, with naturality and diagram transition compatibility, rather
than just unrelated isomorphisms at each vertex.
`conjugate_extendScalarsIdIso_hom` and
`conjugate_extendScalarsCompIso_hom` identify their conjugates exactly with
the inverse restriction transformations. Both follow from the inverse law
of the conjugation equivalence.

## Evaluation formulas

`extendScalarsFunctor_map_app` and `restrictScalarsFunctor_map_app` identify
the component of a scalar-changed diagram morphism with the corresponding
scalar-change functor applied to its component.

The four lemmas `extendScalarsIdIso_hom_app_app`,
`extendScalarsIdIso_inv_app_app`, `extendScalarsCompIso_hom_app_app`, and
`extendScalarsCompIso_inv_app_app` identify both directions of the new
comparisons, evaluated at `D` and `i`, with the existing equivariant sheaf
comparisons at `D.obj i`. The forward identity formula and both composition
formulas expand the inverse conjugation component into unit, functorial map
and counit. The diagram unit/counit component formulas and the morphism
evaluation formulas reduce them to the pointwise definitions. The inverse
identity formula is definitional.

## Units and coherence

Let `e_D` and `c_φ,ψ(D)` denote the forward identity and composition
comparisons, and let `r_D` and `r_φ,ψ(E)` denote the forward restriction
comparisons. `extensionUnit_id` proves

```text
η_id(D) ; U_id.map(e_D) = r_D⁻¹.
```

`extensionUnit_comp` proves

```text
η_(ψ ∘ φ)(D) ; U_(ψ ∘ φ).map(c_φ,ψ(D)) =
  η_φ(D) ; U_φ.map(η_ψ(L_φ D)) ; r_φ,ψ(L_ψ(L_φ D))⁻¹.
```

Both equations hold as compatible diagram morphisms. Their proofs use
extensionality, the evaluation formulas, and the corresponding pointwise
unit equations.

`extendScalarsCompIso_id_left` and `extendScalarsCompIso_id_right` prove
that splitting off extension by the identity ring map and then removing it
gives the identity natural transformation. Their statements explicitly
include the left and right functor unitors, respectively.

`extendScalarsCompIso_assoc` equates the two splittings of a triple ring
composite. One route first splits `(ψ ∘ φ), χ`, then splits `φ, ψ`, and
applies the functor associator. The other first splits `φ, (χ ∘ ψ)` and
then splits `ψ, χ`. The proofs of all three coherence laws use natural
transformation extensionality, diagram morphism extensionality, the
pointwise comparison formulas, and the already proved equivariant sheaf
coherence laws. The associator and unitors are retained in the Lean types.

## Scope

This unit establishes coefficient identity/composition coherence for the
supplied compatible equivariant diagrams over arbitrary commutative rings.
It asserts no flatness, exactness, injective preservation, smoothness or
topology on the group, and no commutation of extension with global sections
or higher cohomology. Mixed geometric/ring coherence, ideal reduction,
coefficient inverse systems and inverse-limit comparisons remain separate
work. An actual Harris coefficient system, Shimura tower specialization,
compact support, and the Harris comparison theorems are not constructed here.
