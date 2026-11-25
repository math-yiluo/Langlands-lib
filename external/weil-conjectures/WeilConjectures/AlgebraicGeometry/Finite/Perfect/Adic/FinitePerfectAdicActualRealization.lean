/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicActualLevels
public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicStalkModels
import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicActualLevelDescent
import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicScalarModel

/-! # Realization of the actual finite quotient levels

Source: Stacks Project, Tags 06YY and 09C6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- Scalar realization and normalized transition comparisons for actual levels.
Source: Stacks Tags 06YY and 09C6.
(blueprint: lem-weil-pbc-finite-perfect-adic-actual-realization). -/
structure FinitePerfectAdicActualRealizationData
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (M : DerivedCategory (CompletedAdicModules X d)) (V : X.Etale)
    (T : FinitePerfectAdicAlgebraTower d)
    (L : FinitePerfectAdicActualLevelData X d M V T) where
  realization : ∀ (U : V.left.ProEt) (W : X.ProEt),
    (W ⟶ finitePerfectAdicChartObject V U) → ∀ n : ℕ,
    DerivedCategory (Sheaf (ProEt.topology U.left)
      (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))))) ⥤
      DerivedCategory (SheafOfModules.{t + 1} ((completedAdicRing X d).over W))
  scalar : ∀ (U : V.left.ProEt) (W : X.ProEt)
    (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ),
    normalizationRestrict (ProEt.topology U.left)
        (RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1))) ⋙
          realization U W f (n + 1) ≅
      realization U W f n
  actual : ∀ (U : V.left.ProEt) (W : X.ProEt)
    (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ),
    (realization U W f n).obj
        ((localProEtaleComparison U.hom (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))).obj (L.K n)) ≅
      (finitePerfectAdicRestrictedTower X d W ((completedAdicReduction X d).obj M)).obj
        (op n)
  model : ∀ (U : V.left.ProEt) (W : X.ProEt)
    (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ),
    (realization U W f n).obj
        ((localProEtaleComparison U.hom (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))).obj
          (finitePerfectAdicEtaleConstant V.left T n)) ≅
      (finitePerfectAdicModelDiagram X d W T).obj (op n)
  actual_normalized : ∀ (U : V.left.ProEt) (W : X.ProEt)
    (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ),
    (realization U W f (n + 1)).map (localProEtaleNormalization U.hom
        (RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1))) (L.dK n)) ≫
      (scalar U W f n).hom.app
        ((localProEtaleComparison U.hom (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))).obj (L.K n)) ≫
      (actual U W f n).hom =
    (actual U W f (n + 1)).hom ≫
      (finitePerfectAdicRestrictedTower X d W ((completedAdicReduction X d).obj M)).map
        (homOfLE (Nat.le_succ n)).op
  model_normalized : ∀ (U : V.left.ProEt) (W : X.ProEt)
    (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ),
    (realization U W f (n + 1)).map (localProEtaleNormalization U.hom
        (RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))
        (finitePerfectAdicEtaleConstantTransition V.left T n)) ≫
      (scalar U W f n).hom.app
        ((localProEtaleComparison U.hom (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))).obj
          (finitePerfectAdicEtaleConstant V.left T n)) ≫
      (model U W f n).hom =
    (model U W f (n + 1)).hom ≫
      (finitePerfectAdicModelDiagram X d W T).map (homOfLE (Nat.le_succ n)).op

/-- The descended actual levels admit scalar realization and both normalized comparison
systems. The etale levels are chosen together with their actual descent comparison.
Source: the coefficient restriction and tensor-balancing part of Tags 06YY and 09C6.
Proof: combine the explicit exact realization and its canonical scalar compositor with
the actual descent theorem and the independent constant-model comparison. The actual
descent theorem chooses the levels together with their comparison, rather than
asserting that arbitrary stalkwise models descend M.
(blueprint: lem-weil-pbc-finite-perfect-adic-actual-realization). -/
theorem finitePerfectAdic_actual_realization
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hφ : ∀ n : ℕ, IsIso (φ n)) (hcompat : FinitePerfectModelsCompatible X d φ)
    (M : DerivedCategory (CompletedAdicModules X d)) (V : X.Etale)
    (T : FinitePerfectAdicAlgebraTower d)
    (hperfect : ∀ n : ℕ, DerivedCategory.IsPerfect (T.level n))
    (hmark : FinitePerfectAdicLevelMarkings X d φ M V T) :
    ∃ L : FinitePerfectAdicActualLevelData X d M V T,
      Nonempty (FinitePerfectAdicActualRealizationData X d M V T L) := by
  obtain ⟨L, ⟨hL⟩⟩ :=
    finitePerfectAdic_actual_level_descent X d φ hφ hcompat M V T hperfect hmark
  obtain ⟨model, hmodel⟩ := finitePerfectAdicScalar_model X d V T hperfect
  exact ⟨L, ⟨{
    realization := finitePerfectAdicScalarRealization X d V
    scalar := finitePerfectAdicScalarCoherence X d V
    actual := hL.actual
    model := model
    actual_normalized := hL.actual_normalized
    model_normalized := hmodel }⟩⟩

end AlgebraicGeometry.Scheme
