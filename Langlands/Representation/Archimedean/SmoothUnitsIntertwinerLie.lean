import Langlands.Representation.Archimedean.SmoothUnitActionDerivative

/-! # Differentiating a continuous equivariant map of genuine smooth carriers -/

noncomputable section

open Filter
open scoped Manifold Topology

set_option autoImplicit false

namespace Langlands.Archimedean.DerivativeSmoothVectors

universe uA uE uF

local notation "I" A:max => 𝓘(ℝ, A)

/-- A continuous full-group intertwiner of genuine smooth carriers preserves every
derived direction for representations of the units of a real normed algebra. -/
def SmoothUnitsIntertwinerLieStatement : Prop :=
  ∀ (A : Type uA) [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [FiniteDimensional ℝ A]
    (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (F : Type uF) [NormedAddCommGroup F] [NormedSpace ℂ F]
    (R : Aˣ →* (E →L[ℂ] E)) (S : Aˣ →* (F →L[ℂ] F)),
    IsContinuousRepresentation R → IsContinuousRepresentation S →
    ∀ (T : DerivativeSmoothVectors (I A) R →L[ℂ] DerivativeSmoothVectors (I A) S),
      (∀ g v, T (representation (I A) R g v) = representation (I A) S g (T v)) →
      ∀ X v, T (operator (I A) R X v) = operator (I A) S X (T v)

theorem smoothUnitsIntertwinerLie : SmoothUnitsIntertwinerLieStatement.{uA, uE, uF} := by
  intro A _ _ _ _ E _ _ F _ _ R S hR hS T hT X v
  let c (t : ℝ) : A := 1 + t • X
  have hc : HasDerivAt c X 0 := by
    simpa only [c, id, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const X).const_add (1 : A)
  have hc₀ : c 0 = (1 : Aˣ).val := by simp [c]
  let f (t : ℝ) := unitsChartAction R (c t, v)
  let q (t : ℝ) := unitsChartAction S (c t, T v)
  have hf : HasDerivAt f (operator (I A) R X v) 0 := by
    simpa only [inv_one, Units.val_one, one_mul, map_one, Module.End.one_apply] using
      hasDerivAt_unitsChartOrbit R hR 1 v hc hc₀
  have hq : HasDerivAt q (operator (I A) S X (T v)) 0 := by
    simpa only [inv_one, Units.val_one, one_mul, map_one, Module.End.one_apply] using
      hasDerivAt_unitsChartOrbit S hS 1 (T v) hc hc₀
  rw [Langlands.Analysis.hasDerivAt_iff_tendsto_slope_tvs] at hf hq
  let L := T.restrictScalars ℝ
  have hEq (t : ℝ) : L (f t) = q t := hT _ _
  have h := (L.continuous.tendsto _).comp hf
  have he : Tendsto (slope q 0) (𝓝[≠] 0) (𝓝 (T (operator (I A) R X v))) :=
    h.congr fun t => by
      exact (L.toLinearMap.slope_comp f 0 t).symm.trans
        (congrArg (fun w => slope w 0 t) (funext hEq))
  exact tendsto_nhds_unique he hq

end Langlands.Archimedean.DerivativeSmoothVectors
