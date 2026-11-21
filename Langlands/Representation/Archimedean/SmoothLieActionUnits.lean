import Langlands.Representation.Archimedean.SmoothUnitActionDerivative
import Mathlib.Algebra.Lie.OfAssociative

/-! # The Lie algebra action on genuine smooth vectors of a units representation -/

noncomputable section

open Filter Set
open scoped Manifold ContDiff Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.DerivativeSmoothVectors

open Langlands.Analysis (hasDerivAt_iff_tendsto_slope_tvs)

variable {A E : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] (R : Aˣ →* (E →L[ℂ] E))

local notation "𝓜" => 𝓘(ℝ, A)
local notation "D" => DerivativeSmoothVectors 𝓜 R
local notation "dR" => operator 𝓜 R

/-- The genuine smooth-vector endomorphism is real linear in the algebra direction. -/
def operatorDirection : A →ₗ[ℝ] Module.End ℂ D where
  toFun := dR
  map_add' X Y := by
    apply LinearMap.ext
    intro v
    apply (toSmooth 𝓜 R).injective
    change (smoothLieDerivativeDirection 𝓜 R (X + Y)) (toSmooth 𝓜 R v) =
      smoothLieDerivativeDirection 𝓜 R X (toSmooth 𝓜 R v) +
        smoothLieDerivativeDirection 𝓜 R Y (toSmooth 𝓜 R v)
    rw [map_add, LinearMap.add_apply]
  map_smul' c X := by
    apply LinearMap.ext
    intro v
    apply (toSmooth 𝓜 R).injective
    change (smoothLieDerivativeDirection 𝓜 R (c • X)) (toSmooth 𝓜 R v) =
      c • smoothLieDerivativeDirection 𝓜 R X (toSmooth 𝓜 R v)
    rw [map_smul, LinearMap.smul_apply]

@[simp]
theorem operatorDirection_apply (X : A) : operatorDirection R X = dR X := rfl

/-- A form of unit covariance convenient for differentiating: no inverse depends on `g`
in the displayed directions. -/
theorem operator_mul_representation_units (g : Aˣ) (Y : A) (v : D) :
    dR ((g : A) * Y) (representation 𝓜 R g v) =
      representation 𝓜 R g (dR (Y * (g : A)) v) := by
  rw [operator_representation_units, inverseConjugationCLM_apply, ← mul_assoc, Units.inv_mul,
    one_mul]

variable [FiniteDimensional ℝ A]

/-- The genuine derivative takes the associative-ring commutator to the commutator
of endomorphisms. -/
theorem operator_commutator_units (hR : IsContinuousRepresentation R) (X Y : A) (v : D) :
    dR (X * Y - Y * X) v = dR X (dR Y v) - dR Y (dR X v) := by
  let c : ℝ → A := fun t => 1 + t • X
  let o : ℝ → D := fun t => unitsChartAction R (c t, v)
  let w : ℝ → D := fun t => dR Y v + t • dR (Y * X) v
  have hc : HasDerivAt c X 0 := by
    simpa only [c, id_eq, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const X).const_add 1
  have hc₀ : c 0 = (1 : Aˣ).val := by simp [c]
  have ho₀ : o 0 = v := by
    simpa only [o, hc₀, map_one, Module.End.one_apply] using unitsChartAction_val R (1 : Aˣ) v
  have hw₀ : w 0 = dR Y v := by simp [w]
  have ho : HasDerivAt o (dR X v) 0 := by
    simpa only [o, inv_one, Units.val_one, one_mul, map_one, Module.End.one_apply] using
      hasDerivAt_unitsChartOrbit R hR (1 : Aˣ) v hc hc₀
  have hw : HasDerivAt w (dR (Y * X) v) 0 := by
    apply hasDerivAt_iff_tendsto_slope_tvs.mpr
    refine (tendsto_const_nhds (x := dR (Y * X) v)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := ht
    simp [slope_def_module, w, inv_smul_smul₀ ht0]
  have hAt : (c 0, v) ∈ range (Units.val : Aˣ → A) ×ˢ (univ : Set D) :=
    ⟨⟨1, hc₀.symm⟩, mem_univ _⟩
  have ho_cont : ContinuousAt o 0 := by
    have hcurve : ContinuousAt (fun t : ℝ => (c t, v)) 0 :=
      hc.continuousAt.prodMk continuousAt_const
    have hchart := (continuousOn_unitsChartAction R hR _ hAt).continuousAt
      ((Units.isOpenEmbedding_val.isOpen_range.prod isOpen_univ).mem_nhds hAt)
    exact hchart.comp (f := fun t : ℝ => (c t, v)) hcurve
  let l : ℝ → D := fun t => dR Y (o t) + t • dR (X * Y) (o t)
  have hL : Tendsto (slope l 0) (𝓝[≠] 0) (𝓝 (dR Y (dR X v) + dR (X * Y) v)) := by
    let L := (operatorCLM 𝓜 R Y).restrictScalars ℝ
    have h₁ := (L.continuous.tendsto (dR X v)).comp (hasDerivAt_iff_tendsto_slope_tvs.mp ho)
    have h₂ : Tendsto (fun t => dR (X * Y) (o t)) (𝓝[≠] 0) (𝓝 (dR (X * Y) v)) :=
      ((operatorCLM 𝓜 R (X * Y)).continuous.tendsto v).comp
        ((ho₀ ▸ ho_cont.tendsto).mono_left nhdsWithin_le_nhds)
    refine (h₁.add h₂).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := ht
    change L (slope o 0 t) + dR (X * Y) (o t) =
      slope (fun u => L (o u) + u • dR (X * Y) (o u)) 0 t
    simp only [slope_def_module, sub_zero, zero_smul, add_zero, add_sub_right_comm,
      smul_add, inv_smul_smul₀ ht0, map_smul, map_sub]
  have hU : HasDerivAt (fun t => unitsChartAction R (c t, w t))
      (dR X (dR Y v) + dR (Y * X) v) 0 := by
    simpa only [hw₀, inv_one, Units.val_one, one_mul, map_one, Module.End.one_apply] using
      hasDerivAt_unitsChartAction R hR (1 : Aˣ) hc hc₀ hw
  have he : (fun t => unitsChartAction R (c t, w t)) =ᶠ[𝓝 0] l := by
    have hm : ∀ᶠ t in 𝓝 0, c t ∈ range (Units.val : Aˣ → A) :=
      hc.continuousAt (Units.isOpenEmbedding_val.isOpen_range.mem_nhds ⟨1, hc₀.symm⟩)
    filter_upwards [hm] with t ht
    obtain ⟨g, hg⟩ := ht
    have hl : (g : A) * Y = Y + t • (X * Y) := by
      rw [hg]
      change (1 + t • X) * Y = _
      rw [add_mul, one_mul, smul_mul_assoc]
    have hr : Y * (g : A) = Y + t • (Y * X) := by
      rw [hg]
      change Y * (1 + t • X) = _
      rw [mul_add, mul_one, mul_smul_comm]
    have hd := operator_mul_representation_units R g Y v
    rw [hl, hr] at hd
    simp only [← operatorDirection_apply R, map_add, map_smul, LinearMap.add_apply,
      LinearMap.smul_apply] at hd
    simpa [l, w, o, ← hg] using hd.symm
  have he' : slope (fun t => unitsChartAction R (c t, w t)) 0 =ᶠ[𝓝[≠] 0] slope l 0 := by
    filter_upwards [he.filter_mono nhdsWithin_le_nhds] with t ht
    rw [slope_def_module, slope_def_module, ht, he.eq_of_nhds]
  have h := tendsto_nhds_unique_of_eventuallyEq hL
    (hasDerivAt_iff_tendsto_slope_tvs.mp hU) he'.symm
  rw [← operatorDirection_apply R, map_sub, LinearMap.sub_apply, operatorDirection_apply,
    operatorDirection_apply]
  exact (sub_eq_sub_iff_add_eq_add).2 (by simpa [add_comm] using h)

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The derived real Lie algebra action on the genuine smooth carrier. -/
def operatorLieHom (hR : IsContinuousRepresentation R) : A →ₗ⁅ℝ⁆ Module.End ℂ D where
  toLinearMap := operatorDirection R
  map_lie' {X Y} := by
    apply LinearMap.ext
    intro v
    exact operator_commutator_units R hR X Y v

@[simp]
theorem operatorLieHom_apply (hR : IsContinuousRepresentation R) (X : A) (v : D) :
    operatorLieHom R hR X v = dR X v := rfl

end Langlands.Archimedean.DerivativeSmoothVectors
