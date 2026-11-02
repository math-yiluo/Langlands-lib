# Module cohomology and actual abelian-sheaf cohomology

Worker 368. This internal comparison concerns an arbitrary actual scheme
`X : Scheme.{u}`, an arbitrary structure-sheaf module `M : X.Modules`,
and every degree `n : ℕ`. It compares the module cohomology defined by
`Modules.DerivedSections.cohomology` with Mathlib's actual Ext-defined
`CategoryTheory.Sheaf.H` of the underlying abelian sheaf.

All declarations are in
`Langlands.AlgebraicGeometry.Modules.AbelianSheafComparison`.
The functor `PushforwardInjectiveAcyclic.toAbSheaf X` is the existing
`SheafOfModules.toSheaf X.ringCatSheaf`. The abelian-sheaf global-sections
functor is the published
`Cohomology.AbelianSheafDerivedSections.globalSections X.toTopCat`,
which evaluates a sheaf at the top open.
The additive instance for `toAbSheaf X` is made explicit from Mathlib's
additive instance for `SheafOfModules.toSheaf`.

`globalSectionsIso X` identifies forgetting the module structure and then
taking abelian global sections with taking module global sections and
then forgetting the action of `Γ(X, ⊤)`. Its components are identity
isomorphisms on the actual groups of sections.

`isZero_rightDerived_toAbSheaf X M q` applies the published generic
positive-degree vanishing lemma for homology-preserving functors.
Module forgetting is additive and preserves finite limits and finite
colimits, so it preserves homology.

`isZero_rightDerived_globalSections_of_injective X J q` proves that
the underlying abelian sheaf of an injective module is acyclic for
abelian global sections. The published module flasqueness theorem
makes that underlying sheaf flasque. The actual Ext-defined higher
cohomology therefore vanishes by `AbelianSheafFlasque`, and the
published `AbelianSheafDerivedSections.HAddEquiv` transports this
vanishing to right-derived abelian global sections.

`forgetDerivedSectionsIso X n` is the natural isomorphism from
module-derived global sections followed by forgetting the target module
structure to right derivation of that composite functor. It applies
`DerivedComparison.rightDerivedCompIso` with the identity functor on
the source and exact forgetting on the target.

`cohomologyIso X M n` composes the preceding isomorphism with the
published `AcyclicResolution.compComparison`. The source-side
forgetful functor is exact, and it carries injective modules to
abelian-global-sections-acyclic objects, as proved above. The published
acyclic-resolution comparison theorem therefore makes this comparison
an isomorphism. This argument does not assume that forgetting module
sheaves preserves injective objects.

`HAddEquiv X M n` is the additive equivalence

```text
Sheaf.H.{u} ((toAbSheaf X).obj M) n
  ≃+ (DerivedSections.cohomology X n).obj M.
```

It composes the published actual Ext/right-derived-global-sections
comparison with the inverse of `cohomologyIso`. Its target is the
underlying additive group of the actual `Γ(X, ⊤)`-module cohomology.
The comparison covers zero and all positive degrees without geometric
hypotheses on the scheme.

The provenance is an internal composition of published Library results
and pinned Mathlib's module and abelian-sheaf constructions. No external
theorem or additional axiom is assumed. This file claims a pointwise
additive comparison; it does not claim naturality or compatibility with
connecting homomorphisms for `HAddEquiv`. The imported Ext comparison
does not provide those compatibility statements. No line-bundle
classification, deformation theorem or Picard representability result
is proved here.
