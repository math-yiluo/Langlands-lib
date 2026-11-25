/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerLimitInterface
import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalCompletedReductionRestriction
import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalAdicEvaluationComparison

/-! # Finite reduction of the completed diagonal limit

Source: the diagonal tower limit proof, paragraphs (1) and (3).
(blueprint: lem-sfb-diagonal-limit-finite-reduction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] diagonalCompletedSource diagonalOrdinaryRlim
  diagonalSourceLimitMap diagonalTargetLimitMap diagonalRootLimitComparison
  diagonalSingleLimitComparison diagonalShiftedSingleLimitComparison
  diagonalCompletedRestriction

/-- Finite quotient comparisons for reduction of any map between the two integral
endpoints. Their units are normalized by the actual derived-limit projections.

Source: blueprint `sk-prop-diagonal-tower-limit.proof.md`, paragraph (3);
Stacks 099I and 099M (blueprint: lem-sfb-diagonal-limit-finite-reduction).
Proof: construct simultaneous derived reduction in the completed module category
using the quotient cokernels and K-flat resolutions, retaining its quotient units.
The two-term free resolution of Z_l/ell^(n+1), and tensor associativity, identify
reduction of the total limit of D.T with its level n. Transport this comparison
through the specified endpoint isomorphisms s, t, a and b. Constant-completion finite
quotient comparison identifies this calculation with completed-coefficient reduction.
The adjoint of each derived-limit projection is the comparison, giving the two unit
equations below. Its naturality square for the strict-system morphism D.T(f), together
with the equation relating delta to Rlim(f), gives the final equality after composing
with the inverse target comparison. This argument is functorial in f and uses no
Cartier cycle class or uniqueness of a completed lift. -/
theorem diagonal_limit_finite_reduction (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpℓ : p ≠ ℓ)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] (hY : IsUnit (ℓ : Γ(Y, ⊤)))
    [HasDerivedCategory.{u + 1} (DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalMod ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalCompleted ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalCompleted ℓ (diagonalSurface Y))]
    [HasExt.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ (diagonalSurface Y)))
    (hcompletion : DiagonalCompletionSpec ℓ (diagonalSurface Y) D)
    (H : DiagonalSystems ℓ (diagonalSurface Y))
    (a : D.T.obj ((DerivedCategory.singleFunctor _ 0).obj (diagonalIntegralSource Y)) ≅
      (DerivedCategory.singleFunctor _ 0).obj (D.ordinary.E.obj (diagonalIntegralSource Y)))
    (b : D.T.obj (((DerivedCategory.singleFunctor _ 0).obj
      (diagonalComparisonUnits Y))⟦(1 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor _ 0).obj H)⟦(2 : ℤ)⟧)
    (L : DiagonalRlim (DiagonalMod ℓ (diagonalSurface Y)))
    (s : (diagonalCompletedRestriction ℓ (diagonalSurface Y)).obj
      (diagonalCompletedSource ℓ Y) ≅ limit (D.ordinary.E.obj (diagonalIntegralSource Y)))
    (t : (diagonalCompletedRestriction ℓ (diagonalSurface Y)).obj
      (Scheme.purTwistZlModule (diagonalSurface Y) ℓ) ≅ limit H)
    (hs : IsIso (diagonalSourceLimitMap ℓ Y D a L s))
    (ht : IsIso (diagonalTargetLimitMap ℓ Y D H b L t)) :
    let F := diagonalCompletedUnderlying ℓ (diagonalSurface Y)
    let E := fun n : ℕ ↦
      ((evaluation ℕᵒᵖ (DiagonalMod ℓ (diagonalSurface Y))).obj (op n)).mapDerivedCategory
    let C := fun n : ℕ ↦
      ((evaluation ℕᵒᵖ (DiagonalCompleted ℓ (diagonalSurface Y))).obj (op n)).mapDerivedCategory
    ∃ M : DiagonalCompletedReduction ℓ (diagonalSurface Y),
      ∀ (f : (DerivedCategory.singleFunctor _ 0).obj (diagonalIntegralSource Y) ⟶
        ((DerivedCategory.singleFunctor _ 0).obj
          (diagonalComparisonUnits Y))⟦(1 : ℤ)⟧)
        (δ : diagonalCompletedDomain ℓ Y ⟶ diagonalCompletedCodomain ℓ Y),
        F.map δ ≫ diagonalTargetLimitMap ℓ Y D H b L t =
          diagonalSourceLimitMap ℓ Y D a L s ≫ L.R.map (D.T.map f) → ∀ n : ℕ,
        ∃ (e : F.obj ((C n).obj (M.derived.T.obj (diagonalCompletedDomain ℓ Y))) ≅
            (E n).obj (D.T.obj
              ((DerivedCategory.singleFunctor _ 0).obj (diagonalIntegralSource Y))))
          (g : F.obj ((C n).obj (M.derived.T.obj (diagonalCompletedCodomain ℓ Y))) ≅
            (E n).obj (D.T.obj
              (((DerivedCategory.singleFunctor _ 0).obj
                (diagonalComparisonUnits Y))⟦(1 : ℤ)⟧))),
          F.map ((M.unit n).app (diagonalCompletedDomain ℓ Y)) ≫ e.hom =
            diagonalSourceLimitMap ℓ Y D a L s ≫ (L.projection n).app _ ∧
          F.map ((M.unit n).app (diagonalCompletedCodomain ℓ Y)) ≫ g.hom =
            diagonalTargetLimitMap ℓ Y D H b L t ≫ (L.projection n).app _ ∧
          F.map ((C n).map (M.derived.T.map δ)) =
            e.hom ≫ (E n).map (D.T.map f) ≫ g.inv := by
  classical
  have _ := hpℓ
  have _ := hY
  let F := diagonalCompletedUnderlying ℓ (diagonalSurface Y)
  let E := fun n : ℕ ↦
    ((evaluation ℕᵒᵖ (DiagonalMod ℓ (diagonalSurface Y))).obj (op n)).mapDerivedCategory
  let C := fun n : ℕ ↦
    ((evaluation ℕᵒᵖ (DiagonalCompleted ℓ (diagonalSurface Y))).obj (op n)).mapDerivedCategory
  obtain ⟨M, N, hα⟩ := diagonal_completed_reduction_restriction ℓ (diagonalSurface Y)
  refine ⟨M, ?_⟩
  intro f δ hδ n
  obtain ⟨α, hαunit⟩ := hα n
  obtain ⟨β, hβunit⟩ := diagonal_adic_evaluation_comparison ℓ (diagonalSurface Y)
    D hcompletion L N n
  let B := N.derived.T ⋙ E n
  let source := diagonalSourceLimitMap ℓ Y D a L s
  let target := diagonalTargetLimitMap ℓ Y D H b L t
  let : IsIso source := hs
  let : IsIso target := ht
  let e := α.app (diagonalCompletedDomain ℓ Y) ≪≫
    B.mapIso (asIso source) ≪≫ β.app _
  let g := α.app (diagonalCompletedCodomain ℓ Y) ≪≫
    B.mapIso (asIso target) ≪≫ β.app _
  refine ⟨e, g, ?_, ?_, ?_⟩
  · change F.map ((M.unit n).app _) ≫
      (α.hom.app _ ≫ B.map source ≫ β.hom.app _) = _
    rw [← Category.assoc, hαunit]
    rw [← (N.unit n).naturality_assoc source]
    rw [hβunit]
    rfl
  · change F.map ((M.unit n).app _) ≫
      (α.hom.app _ ≫ B.map target ≫ β.hom.app _) = _
    rw [← Category.assoc, hαunit]
    rw [← (N.unit n).naturality_assoc target]
    rw [hβunit]
    rfl
  · apply (cancel_mono g.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    change F.map ((C n).map (M.derived.T.map δ)) ≫
      (α.hom.app _ ≫ B.map target ≫ β.hom.app _) =
      (α.hom.app _ ≫ B.map source ≫ β.hom.app _) ≫ (E n).map (D.T.map f)
    have hαδ := α.hom.naturality δ
    change F.map ((C n).map (M.derived.T.map δ)) ≫ α.hom.app _ =
      α.hom.app _ ≫ B.map (F.map δ) at hαδ
    rw [reassoc_of% hαδ]
    change α.hom.app _ ≫ B.map (F.map δ) ≫ B.map target ≫ β.hom.app _ = _
    rw [← B.map_comp_assoc, hδ, B.map_comp_assoc]
    change α.hom.app _ ≫ B.map source ≫
      B.map (L.R.map (D.T.map f)) ≫ β.hom.app _ = _
    have hβf := β.hom.naturality f
    change B.map (L.R.map (D.T.map f)) ≫ β.hom.app _ =
      β.hom.app _ ≫ (E n).map (D.T.map f) at hβf
    rw [hβf]
    simp only [Category.assoc]

end AlgebraicGeometry.ProEtale
