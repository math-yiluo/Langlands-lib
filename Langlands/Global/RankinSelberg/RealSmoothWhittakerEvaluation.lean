import Langlands.Global.RankinSelberg.RealWhittakerStandardEvaluation
import Langlands.Representation.Archimedean.RealSmoothCompactFiniteDensity
import Langlands.Representation.Archimedean.SmoothAction

/-! # Continuous Whittaker evaluation on the smooth standard module -/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open Set
open scoped Matrix.Norms.Operator TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealStandardCompactBanach

open DerivativeSmoothVectors

attribute [local instance 100] LieRing.ofAssociativeRing

private local instance (n : ℕ) (ds : List RealBlock) : NormedAddCommGroup (Carrier n ds) :=
  (closureSubmodule (n := n) ds).normedAddCommGroup

private local instance (n : ℕ) (ds : List RealBlock) : NormedSpace ℂ (Carrier n ds) :=
  (closureSubmodule (n := n) ds).normedSpace

variable {r : ℕ}

local notation "G" => Langlands.GeneralLinear (r + 1) ℝ
local notation "N" => GeneralLinear.upperUnipotent (r + 1) ℝ
local notation "I" => matrixModel ℝ (r + 1)
local notation "V" ds => Automorphic.realStandardKFinite (r + 1) ds
local notation "R" ds => representation (n := r + 1) ds
local notation "D" ds => DerivativeSmoothVectors I (R ds)

/-- The compact-finite standard vectors are dense for the genuine derivative topology. -/
theorem denseRange_compactFiniteEquiv (ds : List RealBlock) :
    DenseRange (fun f : V ds => (compactFiniteEquiv ds f).val) := by
  have hr : range (fun f : V ds => (compactFiniteEquiv ds f).val) =
      (smoothKFinite ℝ (r + 1) (R ds) : Set (D ds)) := by
    ext y
    constructor
    · rintro ⟨f, rfl⟩
      exact (compactFiniteEquiv ds f).property
    · intro hy
      obtain ⟨f, hf⟩ := (compactFiniteEquiv ds).surjective ⟨y, hy⟩
      exact ⟨f, congrArg (fun v : smoothKFinite ℝ (r + 1) (R ds) => v.val) hf⟩
  rw [DenseRange, hr]
  exact realSmoothCompactFiniteDensity (r + 1) (Carrier (r + 1) ds)
    (R ds) (isContinuousRepresentation ds)

/-- Character and coefficient identities for one continuous scalar evaluation. -/
def IsWhittakerStandardEvaluation (ds : List RealBlock) (a : ℝˣ) (B : (V ds) →ₗ[ℂ] (G → ℂ))
    (L : (D ds) →L[ℂ] ℂ) : Prop :=
  (∀ f g, L (DerivativeSmoothVectors.representation I (R ds) g (compactFiniteEquiv ds f).val) =
    B f g) ∧
  ∀ (u : N) (v : D ds),
    L (DerivativeSmoothVectors.representation I (R ds) u.val v) =
      realWhittakerCharacter a u.val * L v

/-- Forgetting the topology of the source of `L` recovers the standard
finite-word formulation of a smooth Whittaker functional. -/
theorem isWhittakerFunctional_of_standardEvaluation (ds : List RealBlock) (a : ℝˣ)
    (B : (V ds) →ₗ[ℂ] (G → ℂ)) (L : (D ds) →L[ℂ] ℂ)
    (hL : IsWhittakerStandardEvaluation ds a B L) :
    IsWhittakerFunctional I (R ds) N
      (Whittaker.standardCharacter (realScaledCharacter a) r)
      (L.toLinearMap.comp (toSmooth I (R ds)).symm.toLinearMap) := by
  let e := toSmooth I (R ds)
  let L₀ := L.toLinearMap.comp e.symm.toLinearMap
  have hcont : Continuous (fun v : D ds => L₀ (e v)) := by
    simpa only [L₀, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      ContinuousLinearMap.coe_coe] using L.continuous
  refine ⟨isContinuousOnSmoothVectors_of_continuous _ _ L₀ hcont, ?_⟩
  intro u v
  have he : e.symm (smoothRepresentation I (R ds) u.val v) =
      DerivativeSmoothVectors.representation I (R ds) u.val (e.symm v) := by
    apply e.injective
    simp only [LinearEquiv.apply_symm_apply, toSmooth_representation, e]
  change L (e.symm (smoothRepresentation I (R ds) u.val v)) =
    realWhittakerCharacter a u.val * L (e.symm v)
  rw [he]
  exact hL.2 u (e.symm v)

/-- The continuous evaluation realizing a given uniform coefficient map
is Whittaker equivariant on the entire smooth standard module and is unique. -/
def RealSmoothWhittakerEvaluationStatement : Prop :=
  RealSmoothCasselmanWallachExtensionStatement.{0, 0, 0} →
    ∀ (m : ℕ) (ds : List RealBlock) (a : ℝˣ)
      (B : Automorphic.realStandardKFinite (m + 1) ds →ₗ[ℂ]
        (Langlands.GeneralLinear (m + 1) ℝ → ℂ)),
      IsIrreducibleGKModule (realStandardRep (m + 1) ds) (realStandardLie (m + 1) ds) →
      IsRealUniformWhittakerIntertwiner m ds a B →
        ∃! L : DerivativeSmoothVectors (matrixModel ℝ (m + 1))
            (representation (n := m + 1) ds) →L[ℂ] ℂ,
          IsWhittakerStandardEvaluation ds a B L

set_option maxHeartbeats 600000 in
theorem realSmoothWhittakerEvaluation : RealSmoothWhittakerEvaluationStatement := by
  intro hCW m ds a B hIrr hB
  obtain ⟨L, hL⟩ := exists_continuous_standardEvaluation hCW ds a B hIrr hB
  have hd := denseRange_compactFiniteEquiv (r := m) ds
  have hOne (f : Automorphic.realStandardKFinite (m + 1) ds) :
      L (compactFiniteEquiv ds f).val = B f 1 := by
    simpa only [map_one, Module.End.one_apply] using hL f 1
  refine ⟨L, ⟨hL, ?_⟩, ?_⟩
  · intro u v
    let T := SmoothAction.derivativeAction (matrixModel ℝ (m + 1)) (representation ds) u.val
    have hLeft : Continuous (fun z => L (T z)) := L.continuous.comp T.continuous
    have hRight : Continuous (fun z => realWhittakerCharacter a u.val * L z) :=
      continuous_const.mul L.continuous
    have he := hd.equalizer hLeft hRight (funext fun f => by
      change L (DerivativeSmoothVectors.representation (matrixModel ℝ (m + 1))
        (representation ds) u.val (compactFiniteEquiv ds f).val) =
          realWhittakerCharacter a u.val * L (compactFiniteEquiv ds f).val
      rw [hL, hOne]
      simpa only [mul_one] using hB.1.1 f u.val u.property 1)
    exact congrFun he v
  · intro L' hL'
    apply ContinuousLinearMap.ext
    intro v
    have he := hd.equalizer L'.continuous L.continuous (funext fun f => by
      rw [Function.comp_apply, Function.comp_apply, hOne]
      simpa only [map_one, Module.End.one_apply] using hL'.1 f 1)
    exact congrFun he v

end Langlands.Global.RankinSelbergGlobal.RealStandardCompactBanach
