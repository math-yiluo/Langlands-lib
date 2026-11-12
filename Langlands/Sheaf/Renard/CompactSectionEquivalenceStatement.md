# Statements: Renard's II.2.5 Theorem on compact sections

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, II.2.5 Theorem and its proof, printed
pp.39–40 / PDF pp.45–46, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The Theorem says that for a t.d. space `X`, `M ↦ M_c(X)` is an equivalence
between sheaves of `C^∞_X`-modules and nondegenerate `D(X)`-modules. The
proof constructs the inverse `M ↦ (U ↦ χ_U · M)` and states that the two
functors are inverse to each other. This file states three closed
propositions over the actual constructed functors and maps. It proves none
of them.

All three quantify over every `X : Type` with a topology and
`hX : Langlands.Topology.IsLocallyProfinite X` (Hausdorff with a basis of
compact open neighborhoods, Renard's t.d. spaces). Complex vector sheaves are
`VectorSheafScalars.VectorSheaf X`, Mathlib's sheaves of complex vector spaces.
Sheaves of complex vector spaces are the same as sheaves of `C^∞_X`-modules
by the II.2.5 Proposition and Remark: `VectorSheafScalars` constructs the
module structure. The universe is `Type` because the published
`CompactSupport` ties the universes.

- `SheafComparisonIsIso`: for every complex vector sheaf `F`, the
  original-sheaf comparison
  `SheafProjectorComparison.sheafComparison F hX :
  F ⟶ (ProjectorVectorSheaf.functor hX).obj ((compactSectionFunctor hX).obj F)`
  is an isomorphism in Mathlib's sheaf category. On a compact open `U ⊆ V`
  the comparison sends `s` to the zero extension of `s|_U`. This is the
  source's final assertion that the sheaf rebuilt from `M = M_c(X)` is the
  original sheaf, `χ_U · M = M(U)`.
- `CompactSectionFunctorIsEquivalence`: the actual compact-section functor
  `CompactSectionTestModule.compactSectionFunctor hX`, from complex vector
  sheaves to the published `NondegenerateModuleCat` of
  `PointwiseTestAlgebra.Carrier X`, is an equivalence of categories
  (Mathlib's `Functor.IsEquivalence`). This is the Theorem's main assertion.
- `ProjectorFunctorIsEquivalence`: the actual inverse functor
  `ProjectorVectorSheaf.functor.{0, 0} hX`, `M ↦ (U ↦ χ_U · M)`, is an
  equivalence of categories.

The module-side comparison `M ⟶ Γc(P M)` and the statement that it is an
isomorphism are a separate unit. No inverse functor laws, comparison
certificates or equivalences are assumed or constructed here. Each
proposition is a target for a later `lean.proof@1` task.

Worker 184 implements these statements for Task 5338.
