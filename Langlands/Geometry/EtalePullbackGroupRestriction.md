# Group restriction and equivariant geometric pullback

This module connects the existing restriction of acting groups with geometric
pullback of actual equivariant small-étale module sheaves. It constructs their
natural interchange isomorphism, restricts geometric coefficient maps, and
proves the corresponding squares on ordinary cohomology and global sections.
All declarations lie in `Langlands.Geometry.EtaleCohomologyAction`.

## Inputs and conventions

Let `X Y : Scheme.{u}` and let `R : Type u` be a commutative ring. The groups
`G : Type w` and `H : Type w'` have independent universes. The scheme actions
are `ρ : G →* (Aut X)ᵐᵒᵖ` and `τ : G →* (Aut Y)ᵐᵒᵖ`. The geometric input is
an étale morphism `f : Y ⟶ X` with

```text
hf g : f ≫ (aut ρ g).hom = (aut τ g).hom ≫ f.
```

The opposite-automorphism convention agrees with the imported framework:
`aut ρ (g*h)` is `aut ρ g` followed by `aut ρ h`. Composition `a ≫ b` first
applies `a`. A group homomorphism `φ : H →* G` supplies the restricted actions
`ρ.comp φ` and `τ.comp φ`; their equivariance equation is `hf (φ h)`.
No topology or injectivity assumption on `φ` is imposed.

The coefficient categories consist of the already constructed
translation-equivariant sheaves of `ModuleCat.{u} R` on the actual small étale
sites. Write `Res_X` and `Res_Y` for the published `restrictionFunctor` on these
categories, and `P_G` and `P_H` for `equivariantPullback` before and after group
restriction. Their ordinary underlying sheaf functor is
`P = EtalePullback.restriction f (ModuleCat.{u} R)`.

## Sheaf interchange and geometric coefficient maps

`restrictionPullbackIso` has type

```text
Res_X ⋙ P_H ≅ P_G ⋙ Res_Y.
```

It is constructed as `Iso.refl`: the two functors are definitionally equal.
Both send `F` to the underlying sheaf `P(F.obj)`. At `h : H`, both structure
maps are the inverse geometric restriction comparison at `φ h`, followed by
`P(F.act (φ h))`. Both send a coefficient morphism `β` to `P(β.hom)`.
The law fields are proofs and agree by proof irrelevance. Thus the comparison
requires no assumed action compatibility beyond the supplied geometric square.
`restrictionPullbackIso_hom_app_hom` and
`restrictionPullbackIso_inv_app_hom` record that both components are identity
maps on the explicitly named sheaf `P(F.obj)`.

For `F` on `X`, `E` on `Y`, and
`α : GeometricCoefficientMap R ρ τ f hf F E`, the definition
`GeometricCoefficientMap.restrictGroup φ α` retains `α.hom : P(F.obj) ⟶ E.obj`
and restricts both coefficient actions. Its compatibility equation at `h`
is exactly `α.comm (φ h)`. The theorem `restrictGroup_hom` records the unchanged
morphism. The theorems `restrictGroup_precomp` and `restrictGroup_postcomp`
show that this construction commutes with source and target coefficient
morphisms after applying the appropriate restriction functor. Both equalities
are definitional, including their proof-valued compatibility fields.

## Cohomology and sections

Write `C_X(F,q)` and `C_Y(E,q)` for the components of the published natural
isomorphisms `restrictionCohomologyFunctorIso`, and `S_X(F)`, `S_Y(E)` for
`restrictionSectionsFunctorIso`. Each comparison has identity underlying module
map. Write `res` for `Action.res (ModuleCat.{u} R) φ`.

For every `q : ℕ`, `GeometricCoefficientMap.restrictGroup_cohomologyMap` proves

```text
H^q(restrictGroup φ α) ≫ C_Y(E,q) = C_X(F,q) ≫ res.map(H^q(α)).
```

Here `H^q(α)` is the published action morphism `α.cohomologyMap q`. Its
underlying map is geometric pullback on ordinary right-derived sections
followed by the ordinary cohomology map of `α.hom`.
`GeometricCoefficientMap.restrictGroup_sectionsMap` proves the analogous
square for `α.sectionsMap` and the comparisons `S_X`, `S_Y`. These proofs use
`Action.Hom.ext`, the published formulas for the underlying geometric maps and
restriction comparisons, and the two categorical identity laws. In the section
case the common underlying map is

```text
(EtalePullback.sectionsMap f R).app F.obj ≫
  (EtaleDerivedSections.sections Y R).map α.hom.
```

Finally, `restrictionPullback_cohomology` proves the square for canonical
geometric pullback itself. Its left route starts with `F` restricted to `H`,
applies the `H`-equivariant geometric pullback, then cohomology of the component
of `restrictionPullbackIso`, and then `C_Y(P_G(F),q)`. Its right route first
applies `C_X(F,q)` and then restricts the original `G`-equivariant geometric
pullback map. `restrictionPullback_sections` gives the same two routes for
sections. After action-morphism extensionality, the component formulas reduce
these identities to preservation of an identity by ordinary cohomology or
sections and the categorical identity laws. The proofs explicitly identify
the ordinary underlying maps before simplifying them.

## Provenance and scope

This is internal infrastructure derived from the published
`EtaleActionRestriction`, `EtaleEquivariantPullback`, `EtaleEquivariantMap` and
`EtaleActionFunctor` constructions. It transcribes no additional theorem from
external literature. The comparisons follow from the actual sheaf formulas;
cohomological compatibility is proved, not supplied as input.

The schemes, ring, group actions and equivariant étale map remain inputs.
Cohomology is the existing ordinary small-étale right-derived global-section
construction equipped with algebraic group actions. This module supplies no
Harris space or level tower, analytic site, topology, smoothness, compact
supports, trace, or comparison with the Harris complexes. It also does not
package higher coherence for successive group restrictions. Those are separate
obligations of the larger framework.
