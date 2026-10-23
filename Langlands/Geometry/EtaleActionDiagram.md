# Equivariant coefficients as a varying-scheme diagram

This module constructs compatible coefficients from an equivariant small-étale
module sheaf, and identifies their cohomology diagram with the existing
cohomology action viewed as a functor from the one-object group category.

## Parameters and variance

Let `Y : Scheme.{u}`, `R : Type u` a commutative ring, `G : Type w` a group,
and `ρ : G →* (Aut Y)ᵐᵒᵖ`. Write `σ_g = aut ρ g`, so that
`σ_(g*h) = σ_g ≪≫ σ_h`. The coefficient category is actual sheaves of
`ModuleCat.{u} R` on `Y.smallEtaleTopology`. There is no topology on `G`.
All cohomology degrees are natural numbers.

`actionSchemeDiagram ρ : SingleObj G ⥤ Scheme.{u}ᵒᵖ` sends the sole object
to `op Y` and an arrow `g` to `σ_g.hom.op`. The one-object category has
composition `g ≫ h = h * g`. Thus the image of a composite is
`(σ_h.hom ≫ σ_g.hom).op`, which is the composite of the two image arrows.
The functor laws follow from `aut_one` and `aut_mul`. Its arrows are étale
because they are underlying morphisms of scheme automorphisms; the module
supplies this instance for the coefficient-diagram interface.

The scheme is constant on objects, but its arrow maps record the given action;
this construction therefore differs from the constant scheme diagram used for
ordinary diagrams of sheaves on a fixed scheme.

## Agreement of restriction constraints

`restrictionCongr_translateCongr` proves that for any equality `h : σ = τ`
of scheme automorphisms, the restriction identification using
`congrArg Iso.hom h` equals the translation identification using `h`.
Restriction and translation have definitionally equal functors at these
automorphisms. The proof eliminates `h`, uses extensionality of the natural
isomorphisms and underlying sheaf morphisms, and finishes with preservation
of the identity by the underlying presheaf.

`actionSchemeDiagram_restrictionId` identifies the diagram restriction unit
with `oneIso R ρ`. It uses the transport comparison at `aut_one ρ`; the
remaining identity restriction and translation constraints agree definitionally.

`actionSchemeDiagram_restrictionComp`, for arrows `g : i ⟶ j` and
`h : j ⟶ k`, identifies the diagram composition constraint with
`compIso R ρ h g`. The order is essential: restriction along `g`, then
restriction along `h`, is translation by `h * g`. The proof applies the
transport comparison at `(aut_mul ρ h g).symm`, after which the original
restriction and translation composition constraints agree definitionally.

## Compatible coefficients

For `F : EquivariantSheaf R ρ`, `ofEquivariant R ρ F` is a
`CoefficientDiagram R (actionSchemeDiagram ρ)` with underlying sheaf `F.obj`
and coefficient arrow `F.act g` for each `g`.

The unit law is `F.act_one` after the unit-constraint comparison. For the
composition law, the imported cocycle equation is

```text
F.act (h * g) = (compIso R ρ h g).inv.app F.obj
  ≫ (translateBy R ρ h).map (F.act g) ≫ F.act h.
```

Composing this equation with the forward constraint and cancelling the
isomorphism gives exactly the required coefficient-diagram composition law.
These obligations concern actual sheaf morphisms; no cohomology maps or
cohomology compatibility laws are assumed as part of this conversion.

## Cohomology comparison

For every `q : ℕ`, `ofEquivariant_cohomology_map` proves that the cohomology
diagram sends `g` to `(pullbackCohomologyAction R ρ F q).ρ g`. Both sides
are the constructed map

```text
cohomologyMapWithCoefficients σ_g.hom R q (F.act g).
```

The left side reduces to this expression by the definitions of the compatible
coefficients and their cohomology diagram. The right side equals it by
`pullbackCohomologyAction_ρ` from `EtaleAutomorphismPullback`.

`ofEquivariantCohomologyIso` is the natural isomorphism from this cohomology
diagram to the functor corresponding to `pullbackCohomologyAction` under
Mathlib's `Action.functorCategoryEquivalence`. Every component is the identity
on `(EtaleDerivedSections.cohomology Y R q).obj F.obj`, and naturality is the
arrow equality just proved.

Finally, `translationCohomologyDiagramIso` is the natural isomorphism from the
functor corresponding to
`TranslationAction.cohomologyAction (sectionsTop R) F (injectiveResolution F.obj) q`
to `(ofEquivariant R ρ F).cohomology q`. It maps the previously constructed
`pullbackCohomologyActionIso` through the action-to-functor equivalence, then
composes with the inverse of `ofEquivariantCohomologyIso`. It is therefore
natural in group arrows and implements the existing canonical cohomology
comparison at the sole object. No category of equivariant sheaves or
naturality in morphisms between such sheaves is constructed in this unit.

## Provenance and scope

This is an internal specialization of `EtaleCohomologyDiagram`, using
`EtaleAutomorphismPullback` and the existing automorphism-translation action.
Its proofs use equality elimination, the actual restriction constraints,
the coefficient cocycle laws and the proved all-degree pullback comparison.
No named original-literature theorem is asserted or assumed.

The input scheme, group action and equivariant sheaf must be supplied.
The construction concerns ordinary small-étale cohomology; it supplies no
Shimura tower, Hecke correspondence, continuous or smooth group action,
compact support, change of coefficients, or derived inverse-limit comparison.
These specializations remain part of the broader framework's obligations.
