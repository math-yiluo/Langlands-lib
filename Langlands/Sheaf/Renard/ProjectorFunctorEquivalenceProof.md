# Renard II.2.5 Theorem: the projector sheaf functor is an equivalence

Worker 111 implemented this proof. The entry theorem is
`Langlands.Sheaf.Renard.CompactSectionEquivalence.projectorFunctorIsEquivalence :
ProjectorFunctorIsEquivalence`. It proves the published proposition
`CompactSectionEquivalence.ProjectorFunctorIsEquivalence` from
`CompactSectionEquivalenceStatement.lean` exactly as stated. That proposition
covers every `X : Type` with a topology satisfying
`Langlands.Topology.IsLocallyProfinite X`. It says that the published functor
`ProjectorVectorSheaf.functor.{0, 0} hX` from
`NondegenerateModuleCat.{0, 0} (PointwiseTestAlgebra.Carrier X)` to
`TopCat.Sheaf (ModuleCat.{0} ℂ) (TopCat.of X)` satisfies Mathlib's
`Functor.IsEquivalence`. The proof adds no further premise.

## Source

The governing original is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, II.2.5. The Theorem
is on printed p.39 / PDF p.45, and its proof runs over printed pp.39–40 /
PDF pp.45–46. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
PDF pp.45–46 were read for this proof.

In the proof of the Theorem, Renard constructs the inverse functor
`M ↦ (U ↦ χ_U · M)` and shows that it lands in sheaves. He then states that
the two functors are inverse to each other, with two checks:

- Starting from a nondegenerate module `M`, `M_c(X) = ⋃_U χ_U · M = M`.
- Starting from a sheaf `M` with `M = M_c(X)`, `χ_U · M = M(U)` for every
  compact open `U`, so the rebuilt sheaf is the original one.

These two checks are the published propositions
`ModuleProjectorComparison.ModuleComparisonIsIso` and
`CompactSectionEquivalence.SheafComparisonIsIso`. This proof imports their
published proofs and assembles the equivalence.

## Imported results

- `CompactSectionEquivalence.sheafComparisonIsIso : SheafComparisonIsIso`,
  from module `Langlands.Sheaf.Renard.SheafComparisonIsIsoProof` (Task 5508).
  For every complex vector sheaf `F`, the comparison
  `SheafProjectorComparison.sheafComparison F hX :
  F ⟶ (ProjectorVectorSheaf.functor.{0, 0} hX).obj ((compactSectionFunctor hX).obj F)`
  is an isomorphism.
- `ModuleProjectorComparison.moduleComparisonIsIso : ModuleComparisonIsIso`,
  from module `Langlands.Sheaf.Renard.ModuleProjectorComparisonProof`
  (Task 5533). For every nondegenerate test module `M`, the comparison
  `ModuleProjectorComparison.moduleComparison hX M :
  M ⟶ (ProjectorVectorSheaf.functor.{0, 0} hX ⋙ compactSectionFunctor hX).obj M`
  is an isomorphism.
- The published natural transformations
  `ModuleProjectorComparison.moduleComparisonNat hX :
  𝟭 _ ⟶ ProjectorVectorSheaf.functor.{0, 0} hX ⋙ compactSectionFunctor hX`
  and `SheafProjectorComparison.sheafComparisonNat hX :
  𝟭 (VectorSheaf X) ⟶ compactSectionFunctor hX ⋙ ProjectorVectorSheaf.functor.{0, 0} hX`.
  Their components are, by definition, `moduleComparison hX M` and
  `sheafComparison F hX`.

## The implemented proof

`projectorFunctorIsEquivalence_of_comparisons` takes
`hS : SheafComparisonIsIso` and
`hM : ModuleProjectorComparison.ModuleComparisonIsIso` as hypotheses and
proves `ProjectorFunctorIsEquivalence`. Fix `X`, its topology and `hX`.

1. Every component `(moduleComparisonNat hX).app M` is `moduleComparison hX M`
   by definition, so `hM X hX M` makes it an isomorphism. In the same way,
   `hS X hX F` makes every component of `sheafComparisonNat hX` an
   isomorphism.
2. Mathlib's `NatIso.isIso_of_isIso_app` turns componentwise isomorphisms
   into isomorphisms of natural transformations. So `moduleComparisonNat hX`
   and `sheafComparisonNat hX` are natural isomorphisms.
3. `CategoryTheory.Equivalence.mk F G η ε` is given these arguments:
   - `F`, the functor `ProjectorVectorSheaf.functor.{0, 0} hX`;
   - `G`, the inverse `compactSectionFunctor hX`;
   - `η`, the supplied unit isomorphism
     `asIso (moduleComparisonNat hX) : 𝟭 ≅ P ⋙ Γc`;
   - `ε`, the supplied counit isomorphism
     `(asIso (sheafComparisonNat hX)).symm : Γc ⋙ P ≅ 𝟭`.

   In the pinned Mathlib, `Equivalence.mk F G η ε` is defined as
   `⟨F, G, adjointifyη η ε, ε, adjointify_η_ε η ε⟩`. It keeps `F`, `G` and
   the counit `ε` unchanged and replaces the unit `η` by `adjointifyη η ε`,
   so that the triangle identity `adjointify_η_ε` holds. In particular, the
   functor of the resulting equivalence is still the published projector
   functor.
4. Mathlib's instance `Equivalence.isEquivalence_functor` then gives
   `(ProjectorVectorSheaf.functor.{0, 0} hX).IsEquivalence`.

The entry theorem `projectorFunctorIsEquivalence` applies
`projectorFunctorIsEquivalence_of_comparisons` to the two imported theorems.
The name is written in full as `CategoryTheory.Equivalence.mk`, because
under `open CategoryTheory` a bare `Equivalence.mk` resolves to the root
constructor for equivalence relations.

## Scope

The proof uses no hypothesis on `X` beyond the published propositions'
`IsLocallyProfinite X`. It adds no compactness, countability or
nonemptiness premise. It assumes no inverse functor law, comparison
certificate or equivalence: the only inputs are the two published
comparison theorems, which are proofs of statements, and Mathlib's
categorical constructions. The universes are those of the statement: `X : Type`,
`NondegenerateModuleCat.{0, 0}` and `ModuleCat.{0} ℂ`. The companion
statement `CompactSectionFunctorIsEquivalence` (Task 5534) is not proved
here.
