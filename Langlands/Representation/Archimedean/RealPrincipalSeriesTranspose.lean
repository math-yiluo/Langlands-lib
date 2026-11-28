import Langlands.Representation.Archimedean.RealPrincipalSeriesCompactAverages
import Langlands.Representation.Archimedean.RealContragredientProof

/-! # Transposing a real principal-series embedding along compact Haar measure -/

noncomputable section

open Langlands.LocalFactor.Archimedean Langlands.KFiniteDual MeasureTheory
open scoped Matrix.Norms.Operator TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.RealPrincipalSeriesTranspose

open RealPrincipalSeriesDuality RealPrincipalSeriesHilbert

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] measurableSpaceK RealPrincipalSeriesDuality.borelSpaceK
attribute [local instance] OrthogonalFinitePolynomial.secondCountableTopology_orthogonal

universe uV

local notation "K" n:max => Matrix.unitaryGroup (Fin n) ℝ
local notation "M" n:max => Matrix (Fin n) (Fin n) ℝ
local notation "G" n:max => Langlands.GeneralLinear n ℝ
local notation "Kc" n:max => unitaryCompact ℝ n
local notation "KF" n:max ds:max => kFiniteFunctions (realStandardModule n ds) (Kc n)

private theorem map_haarOrthogonal (n : ℕ) :
    (haarOrthogonal n).map (orthogonalCompactEquiv n) = haarK n := by
  let e := orthogonalCompactEquiv n
  let μ := haarOrthogonal n
  let ν := μ.map e
  let : ν.IsHaarMeasure := Measure.isHaarMeasure_map_of_isFiniteMeasure μ e.toMonoidHom
    continuous_orthogonalCompactEquiv e.surjective
  let : IsProbabilityMeasure ν := inferInstanceAs (IsProbabilityMeasure (μ.map e))
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure ν (haarK n)

theorem pairing_eq_orthogonal (n : ℕ) (ds es : List RealBlock) (f : KF n ds) (h : KF n es) :
    pairing n ds es f h = ∫ k : K n,
      f.val (Unitary.toUnits k) * h.val (Unitary.toUnits k) ∂haarOrthogonal n := by
  rw [pairing_apply, ← map_haarOrthogonal]
  let e : K n ≃ₜ* Kc n :=
    { orthogonalCompactEquiv n with
      continuous_toFun := continuous_orthogonalCompactEquiv
      continuous_invFun := continuous_orthogonalCompactEquiv_symm }
  exact integral_map_equiv (μ := haarOrthogonal n) e.toHomeomorph.toMeasurableEquiv
    (fun k : Kc n => f.val k.val * h.val k.val)

/-- A compact-finite embedding into a scalar principal series transposes to a map from the
inverse-character scalar series into the algebraic compact-finite dual. -/
def RealPrincipalSeriesTransposeStatement : Prop :=
  ∀ (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (K n) V) (π : (ℂ ⊗[ℝ] M n) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (hgk : IsRealGKModule n ρ π) (cs : List RealCharacterData)
    (B : V →ₗ[ℂ] KF n (cs.map RealBlock.character)),
    IsRealStandardEmbedding n ρ π (cs.map RealBlock.character) B →
    let es := (cs.map RealCharacterData.inverse).map RealBlock.character
    ∃ T : KF n es →ₗ[ℂ] kDual ρ,
      IsRealStandardIntertwiner n (kDualRep ρ) (RealContragredient.dualLie hgk) es T ∧
      ∀ f v, (T f).val v = ∫ k : K n,
        f.val (Unitary.toUnits k) * (B v).val (Unitary.toUnits k) ∂haarOrthogonal n

set_option maxHeartbeats 700000 in
theorem realPrincipalSeriesTranspose : RealPrincipalSeriesTransposeStatement.{uV} := by
  intro n V _ _ ρ π hgk cs B hB es
  let ds := cs.map RealBlock.character
  let Λ : KF n es →ₗ[ℂ] Module.Dual ℂ V := (pairing n es ds).compl₂ B
  have hBK (k : K n) (v : V) : B (ρ k v) = realStandardRep n ds k (B v) := by
    apply Subtype.ext
    exact hB.1 (orthogonalCompactEquiv n k) v
  have hBX (X : M n) (v : V) : B (π (1 ⊗ₜ[ℝ] X) v) =
      realStandardLie n ds (1 ⊗ₜ[ℝ] X) (B v) := by
    apply Subtype.ext
    rw [realStandardLie_one_tmul_apply_coe]
    exact hB.2 X v
  have hK (k : K n) (f : KF n es) (v : V) : Λ (realStandardRep n es k f) (ρ k v) = Λ f v := by
    change pairing n es ds (realStandardRep n es k f) (B (ρ k v)) = pairing n es ds f (B v)
    rw [hBK]
    exact pairing_rightTranslation es ds (orthogonalCompactEquiv n k) f (B v)
      (realStandardRep n es k f).prop (realStandardRep n ds k (B v)).prop
  have hK' (k : K n) (f : KF n es) : Λ (realStandardRep n es k f) = ρ.dual k (Λ f) := by
    apply LinearMap.ext
    intro v
    have he := hK k f (ρ k⁻¹ v)
    simp only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at he
    exact he
  let L : (realStandardRep n es).IntertwiningMap ρ.dual :=
    LinearMap.intertwiningMap_of_isIntertwiningMap _ _ Λ hK'
  let T : KF n es →ₗ[ℂ] kDual ρ := Λ.codRestrict (kDual ρ) (fun f =>
    ((isRealGKModule_realStandardModule n es).1 f).map L)
  refine ⟨T, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro k f
      let j := (orthogonalCompactEquiv n).symm k
      have hj : Unitary.toUnits j = k.val :=
        congrArg Subtype.val ((orthogonalCompactEquiv n).apply_symm_apply k)
      have hm := rightTranslation_mem_kFiniteFunctions_realStandardModule n es f.2 k.prop
      have he : (⟨_, hm⟩ : KF n es) = realStandardRep n es j f := by
        apply Subtype.ext
        rw [realStandardRep_apply_coe, hj]
      refine ⟨hm, ?_⟩
      rw [he]
      apply Subtype.ext
      change Λ (realStandardRep n es j f) = ρ.dual j (Λ f)
      exact hK' j f
    · intro X f
      have hm : rightDerivative (matrixModel ℝ n) X (f : G n → ℂ) ∈
          kFiniteFunctions (realStandardModule n es) (Kc n) := by
        rw [← realStandardLie_one_tmul_apply_coe]
        exact (realStandardLie n es (1 ⊗ₜ[ℝ] X) f).prop
      refine ⟨hm, ?_⟩
      have he : (⟨_, hm⟩ : KF n es) = realStandardLie n es (1 ⊗ₜ[ℝ] X) f :=
        Subtype.ext (realStandardLie_one_tmul_apply_coe n es X f).symm
      rw [he]
      apply Subtype.ext
      apply LinearMap.ext
      intro v
      change Λ (realStandardLie n es (1 ⊗ₜ[ℝ] X) f) v =
        (RealContragredient.dualLie hgk (1 ⊗ₜ[ℝ] X) (T f)).val v
      rw [RealContragredient.dualLie_apply_apply]
      change pairing n es ds (realStandardLie n es (1 ⊗ₜ[ℝ] X) f) (B v) =
        -pairing n es ds f (B (π (1 ⊗ₜ[ℝ] X) v))
      rw [hBX]
      have hm' : rightDerivative (matrixModel ℝ n) X (B v : G n → ℂ) ∈
          kFiniteFunctions (realStandardModule n ds) (Kc n) := by
        rw [← realStandardLie_one_tmul_apply_coe]
        exact (realStandardLie n ds (1 ⊗ₜ[ℝ] X) (B v)).prop
      have he' : (⟨_, hm'⟩ : KF n ds) = realStandardLie n ds (1 ⊗ₜ[ℝ] X) (B v) :=
        Subtype.ext (realStandardLie_one_tmul_apply_coe n ds X (B v)).symm
      have h := pairing_rightDerivative es ds
        (realPositionCharacter_map_inverse_mul cs) X f (B v) hm hm'
      rw [he, he'] at h
      exact eq_neg_of_add_eq_zero_left h
  · intro f v
    exact pairing_eq_orthogonal n es ds f (B v)

end Langlands.Archimedean.RealPrincipalSeriesTranspose
