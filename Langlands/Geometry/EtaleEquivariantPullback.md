# Pullback of equivariant étale coefficient sheaves

This module constructs the pullback functor on translation-equivariant module
sheaves along an equivariant étale scheme morphism. It then constructs the
natural geometric restriction maps on ordinary equivariant cohomology and
sections, and proves compatibility with the canonical degree-zero comparison.
All declarations are in `Langlands.Geometry.EtaleCohomologyAction`.

## Inputs and conventions

The schemes `X` and `Y` have universe `u`. The coefficient ring `R : Type u` is
commutative, and the group `G : Type w` has an independent universe. Its actions
are homomorphisms `ρ : G →* (Aut X)ᵐᵒᵖ` and
`τ : G →* (Aut Y)ᵐᵒᵖ`. As in `EtaleCohomologyAction`, `aut ρ (g * h)` is the
composite of `aut ρ g` followed by `aut ρ h`; translation first by `h` and then
by `g` is compared to translation by `g * h`.

The geometric input is an actual étale morphism `f : Y ⟶ X` with equations
`hf g : f ≫ (aut ρ g).hom = (aut τ g).hom ≫ f`. The underlying categories are
module sheaves on the actual small étale sites. Write `P` for
`EtalePullback.restriction f (ModuleCat R)`, and `T_X(g)`, `T_Y(g)` for the two
translation functors. The previously constructed natural isomorphism
`C_g = equivariantRestrictionIso R ρ τ f hf g` has orientation
`T_X(g) ⋙ P ≅ P ⋙ T_Y(g)`.

## Construction and intrinsic proofs

The two constraint lemmas establish the coherence needed to transport a
coefficient action through `P`. In these equations every isomorphism is
evaluated at the indicated sheaf, and composition is written in execution order.

* `equivariantRestrictionIso_one` proves
  `C_1.inv(F) ≫ P(one_X.hom(F)) = one_Y.hom(P(F))`.
* `equivariantRestrictionIso_mul` proves
  `C_(g*h).inv(F) ≫ P(comp_X(g,h).inv(F)) =
  comp_Y(g,h).inv(P(F)) ≫ T_Y(g)(C_h.inv(F)) ≫ C_g.inv(T_X(h)(F))`.

The proofs apply sheaf and natural-transformation extensionality. After
unfolding the geometric restriction comparisons and translation functors,
their components are images under the underlying presheaf of arrows in the
small étale site. A private equality-transport lemma identifies the inverse
restriction comparison with the image of the opposite of the forward
`MorphismProperty.Over.mapCongr` component. Combining consecutive maps with
presheaf functoriality reduces both coherence equations to the defining
identity maps of the site comparisons. No cohomology equation or equivariant
structure on the target is supplied as an assumption.

`equivariantPullbackObj` takes an equivariant sheaf `F` on `X` to the sheaf
`P(F.obj)` on `Y` with structure map

```text
C_g.inv(F.obj) ≫ P(F.act g).
```

Its unit law follows from `F.act_one` and the unit constraint lemma. Its
multiplication law follows from `F.act_mul`, preservation of composition by
`P`, the multiplication constraint lemma, and naturality of `C_g.inv` at
`F.act h`.

`equivariantPullback` bundles these objects into a functor. A coefficient
morphism `β` is sent to `P(β.hom)`. Its equivariance follows from `β.comm` and
naturality of `C_g.inv`; identity and composition follow from the corresponding
laws of `P`. `equivariantPullback_map_hom` records the underlying morphism.

`equivariantPullbackCoefficient F` is the geometric coefficient map from `F`
to its constructed pullback, with identity underlying coefficient morphism.
Its compatibility square follows by cancellation of `C_g.hom` and `C_g.inv`.
Thus the target coefficient action is constructed, rather than supplied.

## Cohomology, sections and degree zero

For each `q : ℕ`, `equivariantPullbackCohomology q` is a natural transformation

```text
pullbackCohomologyFunctor R ρ q ⟶
  equivariantPullback R ρ τ f hf ⋙ pullbackCohomologyFunctor R τ q.
```

Its component is the published `GeometricCoefficientMap.cohomologyMap` applied
to the canonical identity coefficient map. The component's underlying linear
map is exactly `EtalePullback.cohomologyMap f R q` at `F.obj`, as proved by
`equivariantPullbackCohomology_app_hom`. Naturality reduces to the naturality
of that ordinary derived geometric pullback after simplifying the image of the
identity coefficient morphism.

`equivariantPullbackSections` similarly gives a natural transformation on
ordinary section actions. `equivariantPullbackSections_app_hom` identifies its
underlying map with `EtalePullback.sectionsMap f R` at `F.obj`. Naturality uses
the published ordinary section-restriction transformation.

Finally, `equivariantPullbackCohomology_zero` proves that the degree-zero
cohomology map followed by the canonical target comparison to sections equals
the canonical source comparison followed by the section map. It is the
published degree-zero coefficient-map square specialized to the identity
coefficient map constructed here.

## Provenance and scope

This is an internal derived construction from the published modules
`EtaleEquivariantMap`, `EtalePullback`, `EtaleCohomologyDiagram`,
`EtaleCohomologyAction`, and `TranslationEquivariantCategory`, and their
underlying Mathlib site and sheaf functors. The source is the explicit
restriction-and-translation construction above; this module does not claim to
transcribe a named result from the Harris or Berkovich literature.

The result concerns ordinary small-étale cohomology with algebraic group
actions. The schemes, actions and equivariant étale morphism remain supplied
inputs. It constructs neither composition or identity comparison isomorphisms
between different geometric pullback functors, nor a Shimura tower, an analytic
site, smoothness of the action, compact supports, trace maps or a Harris
specialization. Those remain separate construction obligations in the larger
framework.
