/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEtaleImage
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEvaluationEquation
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEtaleLift
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEtaleNormalization
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEtaleIntegralUniqueness
/-! # Concrete finite étale class identification -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
attribute [local instance] AlgebraicGeometry.ProEtale.diagonalHasLimit
  AlgebraicGeometry.ProEtale.diagonalModLimits
attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  CategoryTheory.Abelian.Ext diagonalFiniteToPadic diagonalForget

private theorem geoCartierChernEquation_unpack
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    {D Z : Scheme.{u}} (i : D ⟶ Z) (hI : i.ker.IsInvertible)
    (hZ : IsUnit (N : Γ(Z, ⊤))) (c : GeoCartierClass A N hA i)
    (hz : GeoCartierChernEquation A N hA i hI hZ c) :
    ∃ c₁ : Ext (Etale.ordinaryFiniteConstant A Z)
        (Scheme.finiteEtaleTateLine Z N A hA) 2,
      (Ext.mk₀ (Etale.ordinaryFiniteIntegralGenerator A Z)).comp
          (c₁.mapExactFunctor (Etale.RawModuleScalarComparison.forget A Z)) (zero_add 2) =
        Etale.supportedKummerChern A N hA i hI hZ ∧
      (Ext.mk₀ (((comparisonUpperStarConstantSheafIso A Z).app
          (ModuleCat.of A A)).hom ≫
        Scheme.proEtaleConstantDirectImageMap i (ModuleCat.{u + 1} A)
          (ModuleCat.of A A))).comp c (zero_add 2) =
        c₁.mapExactFunctor (comparisonUpperStar (ModuleCat.{u + 1} A) Z) := by
  unfold GeoCartierChernEquation at hz
  exact hz

private theorem transport_proposition {α : Sort _} (P : α → Prop) {x y : α}
    (h : x = y) (hx : P x) : P y := by
  rw [← h]
  exact hx

/-- The finite lift and the geometric antecedent have the same etale class.
Source: finite lift, integral normalization, and ordinary finite Chern uniqueness.
(blueprint: lem-sfb-diagonal-trace-concrete-class-identification). -/
theorem diagonalTrace_concreteClass_identification
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (hY : IsUnit (l : Γ(Y, ⊤)))
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (c : SpTowerClasses.Chern l (ULift.{u} (Padic l)) (diagonalSurface Y))
    (hc : SpTowerClasses.FiniteChernNormalization l (ULift.{u} (Padic l)) c)
    (r : Restriction l (ULift.{u} (Padic l)) (diagonalSurface Y))
    (k : Coefficients l (ULift.{u} (Padic l)) (diagonalSurface Y) c r)
    (n : ℕ) (a : SupportedFiniteBoundaryFrame l Y hY c r k n)
    (z : GeoCartierClass (diagonalResidue.{u} l n) (l ^ (n + 1))
      (cartierResidue_cast l (n + 1)) (diagonalImmersion Y))
    (hz : GeoCartierChernEquation (diagonalResidue.{u} l n) (l ^ (n + 1))
      (cartierResidue_cast l (n + 1)) (diagonalImmersion Y)
      (diagonalImmersion_cartier Y) (diagonalSurface_power_unit l Y hY n) z) :
    ∃ c₁ : Ext (Etale.ordinaryFiniteConstant (diagonalResidue.{u} l n)
      (diagonalSurface Y)) (Scheme.finiteEtaleTateLine (diagonalSurface Y)
        (l ^ (n + 1)) (diagonalResidue.{u} l n) (cartierResidue_cast l (n + 1))) 2,
      finiteEvaluationEquation r.F (diagonalFiniteToPadic l n (diagonalSurface Y)) n
        a.coefficient a.line
        (SpTowerClasses.firstChern l (ULift.{u} (Padic l)) c (SpTowerClasses.diagonalPic Y))
        (finiteEtaleProImage (diagonalResidue.{u} l n) (diagonalSurface Y)
          (l ^ (n + 1)) (cartierResidue_cast l (n + 1)) c₁) ∧
      (Ext.mk₀
        (((comparisonUpperStarConstantSheafIso (diagonalResidue.{u} l n)
          (diagonalSurface Y)).app
            (ModuleCat.of (diagonalResidue.{u} l n) (diagonalResidue.{u} l n))).hom ≫
          Scheme.proEtaleConstantDirectImageMap (diagonalImmersion Y)
            (ModuleCat.{u + 1} (diagonalResidue.{u} l n))
            (ModuleCat.of (diagonalResidue.{u} l n) (diagonalResidue.{u} l n)))).comp
          z (zero_add 2) = c₁.mapExactFunctor
            (comparisonUpperStar (ModuleCat.{u + 1} (diagonalResidue.{u} l n))
            (diagonalSurface Y)) := by
  obtain ⟨b, hb⟩ := diagonalTrace_finiteEtale_lift l Y hY c r k n a
    (SpTowerClasses.diagonalPic Y)
  obtain ⟨c₁, hc₁, hz₁⟩ := geoCartierChernEquation_unpack _ _ _ _ _ _ _ hz
  have hbclass := diagonalTrace_finiteEtale_normalization l Y hY c hc r k n a
    (SpTowerClasses.diagonalPic Y) b hb
  have hbc : b = c₁ := finiteEtale_eq_of_integralChern (diagonalResidue.{u} l n)
    (l ^ (n + 1)) (cartierResidue_cast l (n + 1)) (diagonalImmersion Y)
    (diagonalImmersion_cartier Y) (diagonalSurface_power_unit l Y hY n) b c₁ hbclass hc₁
  have hb' := transport_proposition (fun x => finiteEvaluationEquation r.F
      (diagonalFiniteToPadic l n (diagonalSurface Y)) n a.coefficient a.line
      (SpTowerClasses.firstChern l (ULift.{u} (Padic l)) c (SpTowerClasses.diagonalPic Y))
      (finiteEtaleProImage (diagonalResidue.{u} l n) (diagonalSurface Y)
        (l ^ (n + 1)) (cartierResidue_cast l (n + 1)) x)) hbc hb
  exact ⟨c₁, hb', hz₁⟩

end AlgebraicGeometry.ProEtale.DiagonalTrace
