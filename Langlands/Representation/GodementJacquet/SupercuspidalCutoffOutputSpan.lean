import Langlands.Representation.GodementJacquet.SupercuspidalMatrixSmoothingTransfer
import Langlands.Representation.Smooth.SmoothPart.BasicProof
import Langlands.Representation.OrbitSpan

/-! # Spanning by integrated conjugate coefficient cutoffs -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet.Padic

open MeasureTheory HarmonicAnalysis RankinSelberg GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance outputSpanTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance outputSpanValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance outputSpanLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance outputSpanT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance outputSpanDisconnected : TotallyDisconnectedSpace F.Carrier :=
  (padicLatticeGeometry F F.canonicalTopologicalData).1
local instance outputSpanMeasurable : MeasurableSpace F.Carrier := borel _
local instance outputSpanBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance outputSpanGLMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear (n + 1) F.Carrier) := borel _
local instance outputSpanGLBorel (n : ℕ) :
    BorelSpace (GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩

variable {m : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ (GeneralLinear (m + 1) F.Carrier) V)
  (hρ : IsSupercuspidal ρ)
  (ℓ : Module.Dual ℂ V) (hℓ : IsSmoothVector ρ.dual ℓ)

/-- Conjugation transports both entries of the coefficient and preserves the
determinant-unit cutoff. -/
theorem conjugateSupercuspidalCutoffGroupTest_conjugate
    (v : V) (a g : GeneralLinear (m + 1) F.Carrier) :
    conjugateSupercuspidalCutoffGroupTest F ρ hρ (ρ.dual a ℓ)
        (isSmoothVector_apply a hℓ) (ρ a v) (a * g * a⁻¹) =
      conjugateSupercuspidalCutoffGroupTest F ρ hρ ℓ hℓ v g := by
  let T := F.canonicalTopologicalData
  have hnorm : T.determinantNorm (m + 1) (a * g * a⁻¹) =
      T.determinantNorm (m + 1) g := by
    simp only [map_mul, map_inv]
    exact mul_inv_cancel_comm _ _
  by_cases hg : T.determinantNorm (m + 1) g = 1
  · simp only [conjugateSupercuspidalCutoffGroupTest_apply,
      supercuspidalCutoffGroupTest_apply]
    rw [supercuspidalCutoffMatrixTest_apply T (Nat.succ_pos m)
        ρ hρ (ρ.dual a ℓ) (isSmoothVector_apply a hℓ) (ρ a v)
        ⟨a * g * a⁻¹, hnorm.trans hg⟩,
      supercuspidalCutoffMatrixTest_apply T (Nat.succ_pos m) ρ hρ ℓ hℓ v ⟨g, hg⟩]
    congr 1
    change ℓ (ρ a⁻¹ (ρ (a * g * a⁻¹) (ρ a v))) = ℓ (ρ g v)
    simp only [← Module.End.mul_apply, ← map_mul]
    simp
  · rw [conjugateSupercuspidalCutoffGroupTest_eq_zero F ρ hρ
        (ρ.dual a ℓ) (isSmoothVector_apply a hℓ) (ρ a v) _ (by simpa [hnorm] using hg),
      conjugateSupercuspidalCutoffGroupTest_eq_zero F ρ hρ ℓ hℓ v g hg]

/-- Haar conjugation symmetry identifies the translated integrated output with
another output from the same family. -/
theorem integratedConjugateSupercuspidalCutoff_conjugate
    (v w : V) (a : GeneralLinear (m + 1) F.Carrier) :
    Hecke.integratedAction (generalLinearHaar F.Carrier m) ρ hρ.1.1
        (conjugateSupercuspidalCutoffGroupTest F ρ hρ (ρ.dual a ℓ)
          (isSmoothVector_apply a hℓ) (ρ a v)) (ρ a w) =
      ρ a (Hecke.integratedAction (generalLinearHaar F.Carrier m) ρ hρ.1.1
        (conjugateSupercuspidalCutoffGroupTest F ρ hρ ℓ hℓ v) w) := by
  let μ := generalLinearHaar F.Carrier m
  let f := conjugateSupercuspidalCutoffGroupTest F ρ hρ ℓ hℓ v
  let f' := conjugateSupercuspidalCutoffGroupTest F ρ hρ (ρ.dual a ℓ)
    (isSmoothVector_apply a hℓ) (ρ a v)
  change AlgebraicIntegral.integral μ (Hecke.actionIntegrand ρ hρ.1.1 f' (ρ a w)) =
    ρ a (AlgebraicIntegral.integral μ (Hecke.actionIntegrand ρ hρ.1.1 f w))
  rw [← AlgebraicIntegral.integral_linearMap _
    (Hecke.actionIntegrand_finMeasSupp μ ρ hρ.1.1 f w)]
  rw [← AlgebraicIntegral.integral_comp_measurePreserving
    (Hecke.actionIntegrand ρ hρ.1.1 f' (ρ a w))
    (fun g => a * g * a⁻¹) ((generalLinearHaarSymmetries F.Carrier m).2.2.2 a)]
  congr 1
  ext g
  change f' (a * g * a⁻¹) • ρ (a * g * a⁻¹) (ρ a w) =
    ρ a (f g • ρ g w)
  rw [conjugateSupercuspidalCutoffGroupTest_conjugate F ρ hρ ℓ hℓ]
  simp only [map_smul, ← Module.End.mul_apply, ← map_mul]
  simp [f]

/-- A nonzero coefficient gives a nonzero integrated conjugate-cutoff output:
its evaluation by the same functional is the positive norm-square integral. -/
theorem integratedConjugateSupercuspidalCutoff_ne_zero
    (v : V) (hv : ℓ v ≠ 0) :
    Hecke.integratedAction (generalLinearHaar F.Carrier m) ρ hρ.1.1
      (conjugateSupercuspidalCutoffGroupTest F ρ hρ ℓ hℓ v) v ≠ 0 := by
  let f := supercuspidalCutoffGroupTest F ρ hρ ℓ hℓ v
  have hfone : f 1 = ℓ v := by
    change supercuspidalCutoffMatrixTest F.canonicalTopologicalData
      (Nat.succ_pos m) ρ hρ ℓ hℓ v (1 : GeneralLinear (m + 1) F.Carrier).val = _
    simpa using supercuspidalCutoffMatrixTest_apply F.canonicalTopologicalData
      (Nat.succ_pos m) ρ hρ ℓ hℓ v
      (1 : (F.canonicalTopologicalData.determinantNorm (m + 1)).ker)
  have hpos : 0 < ∫ g, ‖f g‖ ^ 2 ∂generalLinearHaar F.Carrier m :=
    (f.continuous.norm.pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero
      (f.hasCompactSupport.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp))
      (fun _ => sq_nonneg _) (x := 1) (by
        simpa only [Pi.pow_apply, hfone, ne_eq, sq_eq_zero_iff, norm_eq_zero] using hv)
  have heval :
      ℓ (Hecke.integratedAction (generalLinearHaar F.Carrier m) ρ hρ.1.1
        (conjugateSupercuspidalCutoffGroupTest F ρ hρ ℓ hℓ v) v) =
      ∫ g, ((‖f g‖ ^ 2 : ℝ) : ℂ) ∂generalLinearHaar F.Carrier m := by
    rw [Hecke.integratedAction_dual]
    apply integral_congr_ae
    filter_upwards [] with g
    by_cases hg : F.canonicalTopologicalData.determinantNorm (m + 1) g = 1
    · have hc : f g = ℓ (ρ g v) :=
        supercuspidalCutoffMatrixTest_apply F.canonicalTopologicalData
          (Nat.succ_pos m) ρ hρ ℓ hℓ v ⟨g, hg⟩
      change starRingEnd ℂ (f g) * ℓ (ρ g v) = _
      rw [← hc]
      simpa only [Complex.ofReal_pow] using Complex.conj_mul' (f g)
    · have hc : f g = 0 :=
        supercuspidalCutoffMatrixTest_apply_of_not_mem F.canonicalTopologicalData
          (Nat.succ_pos m) ρ hρ ℓ hℓ v g hg
      simp only [conjugateSupercuspidalCutoffGroupTest_apply]
      change starRingEnd ℂ (f g) * ℓ (ρ g v) = _
      simp [hc]
  intro hz
  rw [hz, map_zero, integral_complex_ofReal] at heval
  exact hpos.ne' (Complex.ofReal_eq_zero.mp heval.symm)

omit ℓ hℓ in
/-- The span of all actual compact conjugate-cutoff outputs, allowing every
smooth functional and both representation vectors. -/
def supercuspidalCutoffOutputSpan : Submodule ℂ V :=
  Submodule.span ℂ {z | ∃ (ℓ : Module.Dual ℂ V)
    (hℓ : IsSmoothVector ρ.dual ℓ) (v w : V),
    Hecke.integratedAction (generalLinearHaar F.Carrier m) ρ hρ.1.1
      (conjugateSupercuspidalCutoffGroupTest F ρ hρ ℓ hℓ v) w = z}

omit ℓ hℓ in
/-- The output span is stable under the full general linear group. -/
theorem supercuspidalCutoffOutputSpan_apply_mem
    (a : GeneralLinear (m + 1) F.Carrier) (x : V)
    (hx : x ∈ supercuspidalCutoffOutputSpan F ρ hρ) :
    ρ a x ∈ supercuspidalCutoffOutputSpan F ρ hρ := by
  have hle : supercuspidalCutoffOutputSpan F ρ hρ ≤
      (supercuspidalCutoffOutputSpan F ρ hρ).comap (ρ a) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨ℓ, hℓ, v, w, rfl⟩
    exact Submodule.subset_span ⟨ρ.dual a ℓ, isSmoothVector_apply a hℓ,
      ρ a v, ρ a w, integratedConjugateSupercuspidalCutoff_conjugate F ρ hρ ℓ hℓ v w a⟩
  exact hle hx

omit ℓ hℓ in
/-- In an irreducible supercuspidal representation these actual integrated
outputs span every vector. -/
theorem supercuspidalCutoffOutputSpan_eq_top (hi : ρ.IsIrreducible) :
    supercuspidalCutoffOutputSpan F ρ hρ = ⊤ := by
  let S : Subrepresentation ρ :=
    { toSubmodule := supercuspidalCutoffOutputSpan F ρ hρ
      apply_mem_toSubmodule := by
        intro a x hx
        exact supercuspidalCutoffOutputSpan_apply_mem F ρ hρ a x hx }
  rcases eq_bot_or_eq_top S with hS | hS
  · have hall : ∀ v : V, v = 0 := by
      intro v
      by_contra hv
      obtain ⟨ℓ, hℓ, hℓv⟩ := exists_smoothFunctional_ne_zero F ρ hρ.1.1 v hv
      have hm : Hecke.integratedAction (generalLinearHaar F.Carrier m) ρ hρ.1.1
          (conjugateSupercuspidalCutoffGroupTest F ρ hρ ℓ hℓ v) v ∈ S.toSubmodule :=
        Submodule.subset_span ⟨ℓ, hℓ, v, v, rfl⟩
      rw [hS] at hm
      exact integratedConjugateSupercuspidalCutoff_ne_zero F ρ hρ ℓ hℓ v hℓv hm
    apply Submodule.eq_top_iff'.mpr
    intro v
    rw [hall v]
    exact Submodule.zero_mem _
  · exact congrArg Subrepresentation.toSubmodule hS

end Langlands.GodementJacquet.Padic
