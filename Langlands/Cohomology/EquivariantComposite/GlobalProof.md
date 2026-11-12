# Invariant global sections as derived Hom

`equivariantGlobalComposite` proves exactly the published proposition
`Langlands.Cohomology.EquivariantComposite.EquivariantGlobalCompositeStatement`
from `Langlands.Cohomology.EquivariantComposite.Statement`, at its independent
universe parameters `w`, `w'`, and `u`.

For every commutative ring `R`, group `G`, and space `X` in universe `u`,
with the published action and `ContinuousConstSMul` hypotheses, every choice
of the two derived-category models, and every `n : ℕ`, it supplies an additive
isomorphism

```
H^n(X; G, F) ≃+ Hom_{D(Rep R G)}(R, RΓ(X, F)[n])
```

natural in the equivariant sheaf `F`. Here both sides are the actual functors
and objects named in the published proposition: `invariantGlobalDerived`,
`DerivedCategory.singleFunctor` of `Rep.trivial R G R`, and
`DerivedCategory.Plus.ι` of `globalComplex`. The statement's Lean/Markdown
pair and its imports are preserved. The source correspondence with Tohoku V,
Theorem 5.2.1 is documented in that published statement; this file explains
the implemented proof.

## Resolution comparison

For an additive functor `T` between abelian categories whose source has
injective resolutions, `resolutionRightDerivedIso T I n` identifies
cohomology of `T` applied to the integer extension of an injective resolution
`I` with `(T.rightDerived n).obj F`. It first commutes termwise application
with extension by zero using `DerivedPlus.mapExtendIso`, then uses
`extendHomologyIso` to recover cohomology of the natural-indexed complex,
and finally applies the inverse of `I.isoRightDerivedObj T n`.

`resolutionRightDerivedIso_hom_naturality` proves the corresponding
commutative square for every `InjectiveResolution.Hom I J f`. It combines
naturality of the extension comparison, extension homology, and
`isoRightDerivedObj`. This part needs no model of a derived category.

## Computing the comparison

Fix an injective resolution `I` of `F`. Write `S` for the published section
representation functor and `K` for `S` applied termwise to `I.cochainComplex`.
The instance `sectionResolution_isKInjective` proves that `K` is K-injective:
it is zero in degrees below zero and each term is injective. Injectivity of
the terms uses the imported `ConstantAdjunction` construction, which proves
that `S` preserves injective objects. Mathlib's
`CochainComplex.isKInjective_of_injective` then applies.

`globalComparisonOfResolution R G X I n` composes four additive equivalences:

1. The inverse of `resolutionRightDerivedIso` for invariant global sections,
   after forgetting scalar multiplication, identifies the left side with the
   underlying additive group of `H^n(K^G)`.
2. `invariantsHomologyIso` identifies this group with the cohomology of
   termwise additive Hom from the trivial representation to `K`. It uses
   evaluation at `1` and exactness of the forgetful functor from modules to
   additive groups, as explained in `InvariantsHom.md`.
3. `homologyDerivedAddEquiv` from `KInjectiveHomology` identifies that
   cohomology with shifted morphisms from the trivial representation in
   degree zero to `DerivedCategory.Q.obj K`. Its hypothesis holds by the
   K-injective instance just constructed.
4. The inverse of `AcyclicResolution.derivedResolutionIso S I`, shifted by
   `n`, identifies the target with the actual derived global section complex
   in the proposition. Postcomposition by this isomorphism is additive.

## Naturality and the theorem

`globalComparisonOfResolution_naturality` proves the required equality for
an arbitrary map of injective resolutions above `f : F ⟶ F'`. The first
square is the inverse of `resolutionRightDerivedIso_hom_naturality`. The
second is naturality of `invariantsHomologyIso`. The third is
`homologyDerivedAddEquiv_naturality`. Finally,
`AcyclicResolution.derivedResolutionIso_hom_naturality` intertwines the
localized map of section resolutions with the actual map on derived global
section complexes; shifting its inverse square gives the final
postcomposition equality.

The theorem chooses `injectiveResolution F` for each `F` and uses
`DerivedPlus.descHom` to lift every sheaf morphism. Thus the constructed
family has the naturality required by the published proposition, without
adding any hypothesis or relating `w` and `w'` to each other or to `u`.

## Verification

Development check `eec569c6-9ba3-482a-baff-f9fd37867f8e` in environment
`bb168ec3-1031-46d9-816b-5c2ed7bbe1a6` compiled the complete proof with zero
errors and warnings. Declaration inspection reports a theorem with level
parameters `w`, `w'`, `u` and only `propext`, `Classical.choice`, and
`Quot.sound` among its axioms. Formal acceptance additionally requires the
submission's exact-target validation and independent review.
