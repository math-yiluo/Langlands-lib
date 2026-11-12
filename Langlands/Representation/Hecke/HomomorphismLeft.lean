import Langlands.Representation.Hecke.NondegenerateModuleFunctor
import Langlands.Representation.Hecke.LocalUnitsProof
import Langlands.HarmonicAnalysis.GroupAction
import Langlands.Representation.Smooth.Transfer.PullbackProof
import Langlands.Algebra.NondegenerateTensorFunctor
import Langlands.Algebra.RenardHomFunctors
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected

/-! # The left Hecke action attached to a continuous group homomorphism

Renard, 9 July 2026, III.2.1, printed p.70 / PDF p.76.
-/

noncomputable section

open CategoryTheory MeasureTheory MulOpposite

namespace Langlands.Hecke.Homomorphism

universe uG uH v

open Langlands.Algebra HarmonicAnalysis

section Regular

variable {G : Type uG} [Group G] [TopologicalSpace G] [T2Space G]
  [NonarchimedeanGroup G] [LocallyCompactSpace G]

/-- The published left regular action on test functions is smooth. -/
theorem isSmooth_leftTests : IsSmooth (GroupAction.leftTests (G := G)) := by
  classical
  intro f
  obtain ⟨K, _, _, hK⟩ :=
    TestFunction.commonCompactOpenBiInvariance G {f} ⊤
  refine ⟨K, ?_⟩
  intro k
  apply TestFunction.ext
  intro x
  exact (hK f (by simp)).1 k⁻¹ x

/-- The published right regular action on test functions is smooth. -/
theorem isSmooth_rightTests : IsSmooth (GroupAction.rightTests (G := G)) := by
  classical
  intro f
  obtain ⟨K, _, _, hK⟩ :=
    TestFunction.commonCompactOpenBiInvariance G {f} ⊤
  refine ⟨K, ?_⟩
  intro k
  apply TestFunction.ext
  intro x
  simpa using (hK f (by simp)).2 k x

variable [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]

/-- Finite compact-open local units make the actual Haar Hecke algebra idempotented. -/
theorem isIdempotented : IsIdempotented (HeckeAlgebra μ) := by
  classical
  intro s
  obtain ⟨K, hK, _, he, hfix⟩ :=
    HeckeAlgebra.finiteFamilyLocalUnits G μ s ⊤
  refine ⟨⟨HeckeAlgebra.normalizedIndicator μ K hK, he⟩, ?_⟩
  intro f hf
  exact (Idempotent.sandwich_eq_iff _ f).mpr (hfix f hf)

/-- Translation of the first convolution factor is translation of the product. -/
theorem leftTests_mul (g : G) (f b : HeckeAlgebra μ) :
    GroupAction.leftTests g (f * b) =
      (show HeckeAlgebra μ from GroupAction.leftTests g f) * b := by
  apply TestFunction.ext
  intro x
  change (∫ y, f y * b (y⁻¹ * (g⁻¹ * x)) ∂μ) =
    ∫ y, f (g⁻¹ * y) * b (y⁻¹ * x) ∂μ
  rw [← integral_mul_left_eq_self
    (fun y => f (g⁻¹ * y) * b (y⁻¹ * x)) g]
  simp only [inv_mul_cancel_left, mul_inv_rev, mul_assoc]

end Regular

section Along

variable {G : Type uG} [Group G] [TopologicalSpace G] [T2Space G]
  [NonarchimedeanGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  {H : Type uH} [Group H] [TopologicalSpace H] [T2Space H]
  [NonarchimedeanGroup H] [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
  (μG : Measure G) [μG.IsHaarMeasure] (μH : Measure H) [μH.IsHaarMeasure]
  (φ : H →* G) (hφ : Continuous φ)

/-- The smooth left regular representation restricted along the given homomorphism. -/
def leftRepresentation : Representation ℂ H (HeckeAlgebra μG) :=
  (GroupAction.leftTests (G := G)).comp φ

include hφ in
theorem leftRepresentation_isSmooth : IsSmooth (leftRepresentation μG φ) :=
  isSmooth_comp φ hφ isSmooth_leftTests

/-- The canonical left `H(H)`-module on the original Haar Hecke algebra `H(G)`. -/
abbrev leftModule : NonUnitalModule (HeckeAlgebra μH) (HeckeAlgebra μG) :=
  heckeNonUnitalModule μH (leftRepresentation μG φ)
    (leftRepresentation_isSmooth μG φ hφ)

/-- No arbitrary action is supplied: its scalarized formula is the Haar integral. -/
theorem leftModule_apply (a : HeckeAlgebra μH) (f : HeckeAlgebra μG) (x : G) :
    (letI := leftModule μG μH φ hφ; (a • f) x) =
      ∫ h, a h * f ((φ h)⁻¹ * x) ∂μH := by
  exact integratedAction_dual μH (leftRepresentation μG φ)
    (leftRepresentation_isSmooth μG φ hφ) a f
    { toFun := fun f => f x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

theorem leftModule_isNondegenerate :
    letI := leftModule μG μH φ hφ
    IsNondegenerate (HeckeAlgebra μH) (HeckeAlgebra μG) :=
  heckeNonUnitalModule_isNondegenerate μH (leftRepresentation μG φ)
    (leftRepresentation_isSmooth μG φ hφ)

/-- Right convolution is an intertwiner of the restricted left regular representation. -/
def rightMultiplicationIntertwiner (b : HeckeAlgebra μG) :
    (leftRepresentation μG φ).IntertwiningMap (leftRepresentation μG φ) where
  toLinearMap :=
    { toFun := fun f => f * b
      map_add' := fun f g => add_mul f g b
      map_smul' := fun c f => TestFunction.convolution_smul_left μG c f b }
  isIntertwining' h := by
    apply LinearMap.ext
    intro f
    exact (leftTests_mul μG (φ h) f b).symm

local instance : NonUnitalModule (HeckeAlgebra μG)ᵐᵒᵖ (HeckeAlgebra μG) :=
  NonUnitalModule.rightRegular (HeckeAlgebra μG)

/-- The canonical left action commutes with multiplication on the right. -/
theorem left_commutes_regular :
    letI := leftModule μG μH φ hφ
    ActionsCommute (HeckeAlgebra μH) (HeckeAlgebra μG) (HeckeAlgebra μG) := by
  letI := leftModule μG μH φ hφ
  intro a b f
  exact (integratedAction_intertwiner μH
    (leftRepresentation_isSmooth μG φ hφ) (leftRepresentation_isSmooth μG φ hφ)
    (rightMultiplicationIntertwiner μG φ b) a f).symm

/-- Two-sided nondegeneracy of the `H(H)`–`H(G)` bimodule used by `F` and `I`. -/
theorem left_regular_nondegenerate :
    letI := leftModule μG μH φ hφ
    IsNondegenerateBimodule (HeckeAlgebra μH) (HeckeAlgebra μG)
      (HeckeAlgebra μG) :=
  ⟨leftModule_isNondegenerate μG μH φ hφ,
    NondegenerateTensorFunctor.rightRegular_isNondegenerate (isIdempotented μG)⟩

/-- Renard's Hecke forgetful functor, using exactly the published tensor construction. -/
def F : NondegenerateModuleCat.{uG, v} (HeckeAlgebra μG) ⥤
    NondegenerateModuleCat.{uH, max uG v} (HeckeAlgebra μH) := by
  letI := leftModule μG μH φ hφ
  exact NondegenerateTensorFunctor.F (isIdempotented μH)
    (left_commutes_regular μG μH φ hφ) (left_regular_nondegenerate μG μH φ hφ)

/-- Renard's right induction, using exactly the published nondegenerate Hom construction. -/
def I : NondegenerateModuleCat.{uH, v} (HeckeAlgebra μH) ⥤
    NondegenerateModuleCat.{uG, max uG v} (HeckeAlgebra μG) := by
  letI := leftModule μG μH φ hφ
  exact RenardHomFunctors.I (left_commutes_regular μG μH φ hφ) (isIdempotented μG)

end Along

end Langlands.Hecke.Homomorphism
