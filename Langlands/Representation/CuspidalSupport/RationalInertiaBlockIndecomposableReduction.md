# Renard VI.4.5, Corollary, from VI.4.1 and VI.3.2(i): conditional reduction

Author: Worker 1842.

Module `Langlands.Representation.CuspidalSupport.RationalInertiaBlockIndecomposableReduction`,
namespace `Langlands.CuspidalSupport`.

This module derives the published statement `RationalInertiaBlockIndecomposableStatement`
(Renard VI.4.5, Corollary: the inertia block `M(G)[π]` of an irreducible cuspidal `π`
is indecomposable) from two other published statements:

- `RationalSummandHomEquivalenceStatement` (Renard VI.4.1, Theorem). For `π`
  irreducible cuspidal and `ρ` an irreducible smooth representation of `⁰G` with an
  injective equivariant map `j : ρ → π|_{⁰G}`, it gives two things. First, the compact
  induction `Π = ind_{⁰G}^G ρ` lies in the inertia block of the carrier lift of `π`.
  Second, `Hom(Π, •)` (Mathlib's `preadditiveCoyonedaObj`) is an equivalence from that
  block to modules over `(End Π)ᵐᵒᵖ`.
- `RationalNormKernelOrbitStatement` (Renard VI.3.2(i)). Only its first clause is used:
  the restriction of an irreducible `π` to `⁰G` has an irreducible subrepresentation.

Neither statement is proved in the Library at the time of writing, so this module does
not prove the target. It provides the implication
`rationalInertiaBlockIndecomposable_of_homEquivalence hEq hOrbit`, where
`hEq : RationalSummandHomEquivalenceStatement.{uF, uV}` and
`hOrbit : RationalNormKernelOrbitStatement.{uF, uV}`. Its conclusion is
`RationalInertiaBlockIndecomposableStatement.{uF, uV}` with all of the target's
quantifiers, premises and universes. The named proposition
`RationalInertiaBlockIndecomposableReductionClause.{uF, uV}` is this implication,
`RationalSummandHomEquivalenceStatement.{uF, uV} → RationalNormKernelOrbitStatement.{uF, uV}
→ RationalInertiaBlockIndecomposableStatement.{uF, uV}`. The module proves it as
`rationalInertiaBlockIndecomposableReductionClause_holds`. The third input, the domain property of `End Π`
(Renard VI.4.3, Corollary (i)), is the published theorem
`rationalNormKernelEnd_isDomain : RationalNormKernelEndDomainStatement.{uF, uV}`.

Source: David Renard, *Représentations des groupes réductifs p-adiques* (registered
source `renard-2026-representations-groupes-reductifs-padiques`). The references are
VI.4.5, Corollary (printed p.160 / PDF p.166), VI.4.1 (printed pp.149–151 / PDF
pp.155–157), VI.4.3 (printed pp.154–155 / PDF pp.160–161) and VI.3.2 (printed
pp.143–144 / PDF pp.149–150).

Provenance: derived. Renard's proof uses that the center `Z` of `A = End(Π)` is a
domain, so it has no nontrivial idempotent. The implemented proof uses instead that
the center of the block embeds into `End Π` by evaluation (faithfulness of
`Hom(Π, •)`) and that `End Π` itself has no zero divisors. The categorical step is
`Langlands.Renard.exists_isZero_of_decomposition_fullSubcategory` in
`Langlands.CategoryTheory.Renard.DecompositionCenterIdempotent`, also a separate unit.

## The summand ρ

The irreducible `ρ` and its injective map into the restriction are built from `W` by
`restrictionSummand`, `restrictionSummandι`, `restrictionSummandι_injective` and
`restrictionSummand_isIrreducible` of the module
`Langlands.Representation.CuspidalSupport.RationalNormKernelSummand`. That module is a
separate unit with its own Markdown.

## Proof of the implication

After introducing the target's binders (the field `F`, `G`, the torus data, the
topological instances, `ν`, `hStandard`, `hRoots`, `hU`, `π`, `hπ`, the cuspidality
proof and a decomposition `hP : Renard.IsCategoryDecomposition P` with
`P : Bool → ObjectProperty (RationalInertiaBlock G (rationalInertiaBaseLift G π))`):

1. The first clause of `hOrbit F G hG π hπ` gives an irreducible
   `W : Subrepresentation (π.representation.comp (rationalCommonNormKernel G).subtype)`.
2. Let `ρ = restrictionSummand H π W` with `H = rationalCommonNormKernel G`. It is
   irreducible, and `restrictionSummandι H π W` is an injective map
   `ρ ⟶ SmoothRep.restrictSubgroup H π`.
3. `hEq` applied to `ρ` and this map gives the block membership `hmem` of
   `Π = (Induction.compactInductionFunctor H).obj (SmoothRep.toRep.obj ρ)`. It also
   gives the instance that `preadditiveCoyonedaObj ⟨Π, hmem⟩` is an equivalence, hence
   faithful.
4. `rationalNormKernelEnd_isDomain F G hG ρ hρ` gives `IsDomain (End Π)`, hence
   `NoZeroDivisors (End Π)`.
5. `Renard.exists_isZero_of_decomposition_fullSubcategory ⟨Π, hmem⟩ hP` concludes:
   some `b : Bool` has only zero objects in `P b`.
