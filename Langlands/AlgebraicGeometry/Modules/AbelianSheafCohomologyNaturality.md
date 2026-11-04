# Coefficient naturality of actual module and abelian-sheaf cohomology

Worker 368. This internal companion proves coefficient naturality of the
existing `Modules.AbelianSheafComparison.HAddEquiv`. The actual scheme
`X : Scheme.{u}`, its structure-sheaf modules `M` and `N`, the module
morphism `f : M ⟶ N`, and the degree `n : ℕ` are arbitrary.
No properness, flatness, coherence, injectivity or other geometric or
coefficient hypothesis is added.

All declarations are in
`Langlands.AlgebraicGeometry.Modules.AbelianSheafComparison`.
`toAbSheaf X` is the existing functor forgetting the structure-sheaf
module action. The source is Mathlib's actual Ext-defined
`Sheaf.H.{u} ((toAbSheaf X).obj M) n`, and its coefficient map is
`Sheaf.H.map ((toAbSheaf X).map f) n`. The target is the additive group
underlying the actual `Γ(X, ⊤)`-module
`(DerivedSections.cohomology X n).obj M`, with its actual functor map.

`HAddEquiv_naturality X f n a` proves

```text
HAddEquiv X N n (Sheaf.H.map ((toAbSheaf X).map f) n a)
  = (DerivedSections.cohomology X n).map f (HAddEquiv X M n a).
```

It uses precisely the published pointwise comparison. That comparison
first applies `AbelianSheafDerivedSections.HAddEquiv` to the underlying
abelian sheaf, then the inverse of `cohomologyIso X M n`.
The proof expands this composite, applies the coefficient naturality
of the first equivalence, and evaluates the published
`cohomologyIso_inv_naturality X f n` on the resulting element.
No replacement comparison is chosen.

`HAddEquiv_symm_naturality X f n a` proves the inverse equation

```text
(HAddEquiv X N n).symm ((DerivedSections.cohomology X n).map f a)
  = Sheaf.H.map ((toAbSheaf X).map f) n ((HAddEquiv X M n).symm a).
```

It follows by applying the injective forward equivalence and using
forward naturality and the inverse identities. Both equations hold
in degree zero and every positive degree.

`HNatIso X n` assembles these unchanged components into a natural
isomorphism of functors to `AddCommGrpCat.{u}`:

```text
toAbSheaf X ⋙ Sheaf.functorH (Opens.grothendieckTopology X.toTopCat) n
  ≅ DerivedSections.cohomology X n
      ⋙ forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u}.
```

The construction uses `NatIso.ofComponents` and the forward equation.
`HNatIso_app` identifies the component at `M` with the published
`(HAddEquiv X M n).toAddCommGrpIso` by reflexive equality.
The comparison is additive; no module structure on the source is
asserted.

The provenance is an internal composition of the existing module
comparison, its derived-comparison naturality from
`AbelianSheafComparisonNaturality`, and actual abelian-sheaf
cohomology naturality from `AbelianSheafDerivedSectionsNaturality`.
The last comparison ultimately uses the published naturality of the
actual Ext/right-derived comparison and naturality of the existing
Hom/global-sections derived isomorphism. No new external theorem or
additional axiom is assumed.
Scheme base change, compatibility with connecting homomorphisms,
scalar stability of boundary images and Picard representability remain
separate obligations.
