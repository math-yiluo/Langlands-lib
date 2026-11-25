/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Scalar.RationalP1ScalarChernMaps
public import WeilConjectures.AlgebraicGeometry.RationalP1.Scalar.RationalP1ScalarChernQSplitting
public import WeilConjectures.AlgebraicGeometry.RationalP1.Scalar.RationalP1ScalarChernP2Splitting

/-! # The two scalar unit/Chern splittings
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

attribute [local irreducible] coefficient line diagram trace singleUnitIso
attribute [local irreducible] moduleObjectDerivedPullback moduleObjectDerivedPushforward
attribute [local irreducible] firstProjection secondProjection square condensedAmbientExchange

/-- The unit and the independently transported positive Chern adjunct split each
projective direct image.
This asserts no compatibility between q and p2 and contains no exchange map.
The Chern-degree-one equations are proved separately in ScalarChernDegree;
the trace-zero unit values follow from negative Ext vanishing. -/
theorem scalar_chern_splittings
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)] [IsNoetherian (diagonalSurface Y)]
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (δ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y)
    (family : Family l Y) (r : Reference l Y δ family)
    (a : DiagonalTrace.completedUnit l Y ⟶
      r.tq.Rc.R.obj ((DiagonalTrace.completedLine l (ProjectiveLine Y)) ⟦(2 : ℤ)⟧))
    (ha : CompletedChernNormalized l r.tq.toPresentation a)
    (b : DiagonalTrace.completedUnit l (ProjectiveLine Y) ⟶
      r.t₂.Rc.R.obj ((DiagonalTrace.completedLine l (diagonalSurface Y)) ⟦(2 : ℤ)⟧))
    (hb : CompletedChernNormalized l r.t₂.toPresentation b) :
    let Λ := (coefficient l c).X
    let L := line l c
    let T := fun X : Scheme.{u} ↦
      ((DerivedCategory.singleFunctor (Modules Λ X) 0).obj (L X)) ⟦(2 : ℤ)⟧
    let uq := scalarTwistedUnit Λ (ProjectiveLine Y ↘ Y) (T Y) (T (ProjectiveLine Y))
      (scalarQLineIso l c k p hpl Y)
    let u₂ := scalarTwistedUnit Λ (secondProjection Y)
      (T (ProjectiveLine Y)) (T (diagonalSurface Y)) (secondLineComparison l c k p hpl Y)
    let cq := scalarQChern l c Y r a
    let c₂ := scalarP2Chern l c Y r b
    IsIso (biprod.desc uq cq) ∧ IsIso (biprod.desc u₂ c₂) := by
  exact ⟨scalar_q_chern_splitting l c k p hpl Y δ family r a ha b hb,
    scalar_p2_chern_splitting l c k p hpl Y δ family r a ha b hb⟩

end AlgebraicGeometry.ProEtale.RationalP1
