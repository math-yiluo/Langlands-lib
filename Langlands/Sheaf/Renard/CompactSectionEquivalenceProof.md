# Proof: Renard's II.2.5 Theorem, the compact-section functor is an equivalence

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, II.2.5 Theorem and its proof, printed
pp.39–40 / PDF pp.45–46, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The Theorem says that for a t.d. space `X`, `M ↦ M_c(X)` is an equivalence
between sheaves of `C^∞_X`-modules and nondegenerate `D(X)`-modules. Its proof
constructs the inverse functor `M ↦ (U ↦ χ_U · M)` and checks, in its last
paragraph, that the two composites give back the original sheaf and the
original module.

## Result

`compactSectionFunctorIsEquivalence` proves the unchanged published
proposition `CompactSectionEquivalence.CompactSectionFunctorIsEquivalence`:
for every `X : Type` with a topology and every
`hX : Langlands.Topology.IsLocallyProfinite X`, the published functor
`CompactSectionTestModule.compactSectionFunctor hX :
VectorSheafScalars.VectorSheaf X ⥤
NondegenerateModuleCat.{0, 0} (PointwiseTestAlgebra.Carrier X)`
satisfies Mathlib's `Functor.IsEquivalence`. No premise is added: there is no
compactness, countability or nonemptiness hypothesis on `X`, and no inverse
functor law, comparison certificate or equivalence is assumed.

## Implemented proof

The proof uses the two published comparison isomorphisms of the last paragraph
of Renard's proof, imported by Lean name:

- `CompactSectionEquivalence.sheafComparisonIsIso : SheafComparisonIsIso`
  (module `SheafComparisonIsIsoProof`): every component
  `SheafProjectorComparison.sheafComparison F hX : F ⟶ P(Γc F)` is an
  isomorphism;
- `ModuleProjectorComparison.moduleComparisonIsIso : ModuleComparisonIsIso`
  (module `ModuleProjectorComparisonProof`): every component
  `ModuleProjectorComparison.moduleComparison hX M : M ⟶ Γc(P M)` is an
  isomorphism.

The file has three steps.

- `equivalenceOfComparisons hX`: assuming (as instance arguments) that the
  published natural transformations
  `SheafProjectorComparison.sheafComparisonNat hX :
  𝟭 _ ⟶ compactSectionFunctor hX ⋙ ProjectorVectorSheaf.functor hX` and
  `ModuleProjectorComparison.moduleComparisonNat hX :
  𝟭 _ ⟶ ProjectorVectorSheaf.functor hX ⋙ compactSectionFunctor hX` are
  isomorphisms, Mathlib's `CategoryTheory.Equivalence.mk` builds an
  equivalence with functor `compactSectionFunctor hX`, inverse
  `ProjectorVectorSheaf.functor hX`, unit `asIso (sheafComparisonNat hX)` and
  counit the inverse of `asIso (moduleComparisonNat hX)`.
  `Equivalence.mk` replaces the unit by its adjointified form, so no triangle
  identity is needed. `equivalenceOfComparisons_functor` records that its
  functor is `compactSectionFunctor hX` by definition.
- `compactSectionFunctorIsEquivalence_of_comparisons`: from
  `SheafComparisonIsIso` and `ModuleComparisonIsIso`, for given `X` and `hX`
  every component of both natural transformations is an isomorphism (their
  components are `sheafComparison F hX` and `moduleComparison hX M` by
  definition), so both are isomorphisms by `NatIso.isIso_of_isIso_app`, and
  `Equivalence.isEquivalence_functor` applied to `equivalenceOfComparisons hX`
  gives `(compactSectionFunctor hX).IsEquivalence`.
- `compactSectionFunctorIsEquivalence`: the previous theorem applied to the
  two published proofs.

The universe is `Type`, as in the statement. The equivalence statement for the
projector functor `ProjectorVectorSheaf.functor hX`
(`ProjectorFunctorIsEquivalence`) and the stalk quotient statement are
separate results and are not proved here.
