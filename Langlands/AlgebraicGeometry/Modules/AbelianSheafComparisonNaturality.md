# Coefficient naturality of the module/abelian-sheaf derived comparison

This internal prerequisite assembles the existing pointwise
`AbelianSheafComparison.cohomologyIso` into a natural isomorphism.
It concerns the right-derived global-sections functors and retains exactly
the components of that published comparison.

Fix a scheme `X : Scheme.{u}` and `n : ℕ`. Put

- `U = PushforwardInjectiveAcyclic.toAbSheaf X`, the functor taking an actual
  sheaf of modules to its underlying abelian sheaf;
- `V = forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u}`;
- `Dⁿ = DerivedSections.cohomology X n`, the right-derived module
  global-sections functor;
- `Aⁿ = (AbelianSheafDerivedSections.globalSections X.toTopCat).rightDerived n`.

There are no further hypotheses on `X` or the modules. The common universe
`u` and every nonnegative degree `n` are arbitrary.

## Declarations

`cohomologyIso_hom_naturality` proves, for every coefficient morphism
`f : M ⟶ N`,

```text
V(Dⁿ(f)) ≫ (cohomologyIso X N n).hom
  = (cohomologyIso X M n).hom ≫ Aⁿ(U(f)).
```

`cohomologyIso_inv_naturality` gives the corresponding equation for the
inverse components:

```text
Aⁿ(U(f)) ≫ (cohomologyIso X N n).inv
  = (cohomologyIso X M n).inv ≫ V(Dⁿ(f)).
```

Both equations have `@[reassoc]` companion lemmas.

`cohomologyNatIso X n` is the natural isomorphism

```text
Dⁿ ⋙ V ≅ U ⋙ Aⁿ.
```

`cohomologyNatIso_app` says its component at `M` is exactly the published
`cohomologyIso X M n`.

## Implemented proof and provenance

The published pointwise comparison is the composite of
`forgetDerivedSectionsIso X n` and the isomorphism associated to
`AcyclicResolution.compComparison`. The first factor is already a natural
isomorphism. The second is natural by the published
`compComparison_naturality` from
`Langlands.AlgebraicGeometry.Modules.CohomologyBaseChange`.
For that theorem, exact module forgetting supplies the vanishing assumptions
through the existing `isZero_rightDerived_toAbSheaf X M` and its counterpart
for `N`. The proof composes these two naturality equations. Inverse
naturality follows by cancellation with the isomorphism components.
`NatIso.ofComponents` then assembles the unchanged components.

This is a direct formal consequence of published constructions; no new
external literature assertion is introduced.

## Scope

The right-hand functor here is right-derived global sections of the
underlying abelian sheaf. The existing `HAddEquiv` additionally uses the
pointwise Ext/right-derived comparison in `ExtRightDerived` and
`AbelianSheafDerivedSections`. Naturality of those additional comparison
maps is not proved here. This module therefore makes no claim about
naturality of `HAddEquiv`, base-change compatibility, multiplicative unit
boundaries, Picard lifting fibres, scalar stability of boundary images,
or the final fppf Picard representability theorem.
