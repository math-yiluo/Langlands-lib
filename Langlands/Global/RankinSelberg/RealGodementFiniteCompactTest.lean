import Langlands.Global.RankinSelberg.RealGodementCanonicalColumn

/-! # Compact K-finite Schwartz tests give spectral Godement generators -/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear
open MeasureTheory Set
open scoped Manifold Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

open RealGodementProfiles RealJacquetFrobenius

variable {m : ℕ}

local notation "G" => Langlands.GeneralLinear m ℝ
local notation "H" => Langlands.GeneralLinear (m + 1) ℝ
local notation "K" => unitaryCompact ℝ (m + 1)
local notation "X" => Matrix (Fin m) (Fin (m + 1)) ℝ
local notation "U" => Matrix.unitaryGroup (Fin m) ℝ
local notation "P" => (Fin (m + 1) → ℂ)

/-- The upper right action on the rectangular Schwartz test space. -/
def rectangularRightRepresentation : Representation ℂ H 𝓢(X, ℂ) where
  toFun g := (rectangularTranslateCLM 1 g).toLinearMap
  map_one' := by
    apply LinearMap.ext
    intro Φ
    ext x
    change Φ ((1 : G).val * x * (1 : H).val) = Φ x
    simp
  map_mul' g h := by
    apply LinearMap.ext
    intro Φ
    ext x
    change Φ ((1 : G).val * x * (g * h).val) = Φ ((1 : G).val * ((1 : G).val * x * g.val) * h.val)
    simp only [Units.val_one, Units.val_mul, Matrix.one_mul, Matrix.mul_assoc]

local notation "ρ" => rectangularRightRepresentation (m := m)

@[simp] theorem rectangularRightRepresentation_apply (g : H) (Φ : 𝓢(X, ℂ)) (x : X) :
    (ρ g Φ) x = Φ (x * g.val) := by
  change Φ ((1 : G).val * x * g.val) = _
  simp only [Units.val_one, Matrix.one_mul]

private theorem determinantWeight_leading_onCompact (p : Fin 2) (z : ℂ) (k : K) :
    determinantWeight (charData p z) ((m : ℂ) / 2) k.val =
      determinantWeight (charData p 0) ((m : ℂ) / 2) k.val := by
  rw [determinantWeight_exponent_shift p _ z 0 k.val]
  simp only [MaximalParabolicIntegration.abs_det_unitary k, Real.log_one, Complex.ofReal_zero,
    mul_zero, Complex.exp_zero, mul_one]

section Generator

variable [MeasurableSpace (Langlands.GeneralLinear m ℝ)] [BorelSpace (Langlands.GeneralLinear m ℝ)]
variable (μ : Measure (Langlands.GeneralLinear m ℝ)) [IsFiniteMeasureOnCompacts μ]

private def compactTestEvaluation (c : Langlands.LocalFactor.Archimedean.RealCharacterData) (f : G → ℂ)
    (hf : Continuous f) (T : Set G) (hT : IsCompact T) : 𝓢(X, ℂ) →ₗ[ℂ] ℂ := by
  let F (Ψ : 𝓢(X, ℂ)) (h : G) := f h⁻¹ * determinantWeight c (((m : ℂ) + 1) / 2) h *
    Ψ (rowPoint h.val (1 : H))
  have hR : Continuous (fun h : G => rowPoint h.val (1 : H)) :=
    Units.continuous_val.matrix_mul continuous_const
  have hi (Ψ : 𝓢(X, ℂ)) : IntegrableOn (F Ψ) T μ :=
    (((hf.comp continuous_inv).mul (contMDiff_determinantWeight c _).continuous).mul
      (Ψ.continuous.comp hR)).continuousOn.integrableOn_compact hT
  refine { toFun := fun Ψ => ∫ h in T, F Ψ h ∂μ, map_add' := ?_, map_smul' := ?_ }
  · intro Ψ Ψ'
    rw [← integral_add (hi Ψ) (hi Ψ')]
    refine integral_congr_ae (ae_of_all _ fun h => ?_)
    simp only [F, add_apply, mul_add]
  · intro b Ψ
    rw [← integral_smul]
    refine integral_congr_ae (ae_of_all _ fun h => ?_)
    simp only [F, smul_apply, RingHom.id_apply, smul_eq_mul]
    rw [mul_left_comm]

end Generator

/-- A compact full-rank test with a finite right compact orbit and a fixed lower
profile gives a spectral Godement generator in one common finite left-stable space. -/
def RealGodementFiniteCompactTestStatement (m : ℕ) : Prop :=
  ∀ [MeasurableSpace (Langlands.GeneralLinear m ℝ)] [BorelSpace (Langlands.GeneralLinear m ℝ)]
    (μ : Measure (Langlands.GeneralLinear m ℝ)) [IsFiniteMeasureOnCompacts μ]
    (p : Fin (m + 1) → Fin 2) (φ : Matrix.unitaryGroup (Fin m) ℝ → ℂ),
    IsCompactProfile (fun i => p i.succ) φ →
    ∀ (S : Set (Matrix (Fin m) (Fin (m + 1)) ℝ)), IsCompact S → (∀ x ∈ S, HasFullRowRank x) →
    ∀ (Φ : 𝓢(Matrix (Fin m) (Fin (m + 1)) ℝ, ℂ)), (∀ x ∉ S, Φ x = 0) →
      Φ ∈ kFiniteVectors rectangularRightRepresentation (unitaryCompact ℝ (m + 1)) →
      ∃ (W : Submodule ℂ (unitaryCompact ℝ (m + 1) → ℂ)), FiniteDimensional ℂ W ∧
        (∀ f ∈ W, ∀ q : unitaryCompact ℝ (m + 1),
          (fun k : unitaryCompact ℝ (m + 1) => f (q * k)) ∈ W) ∧
        ∃ C : SpectralSectionFamily μ p W, C.lower = φ ∧ C.test = Φ

theorem realGodementFiniteCompactTest : RealGodementFiniteCompactTestStatement m := by
  intro _ _ μ _ p φ hφ S hS hRank Φ hZero hΦ
  let V := Submodule.span ℂ (range fun k : K => ρ k.val Φ)
  let : FiniteDimensional ℂ V := (mem_kFiniteVectors_iff _ _ _).mp hΦ
  let v (k : K) : V := ⟨ρ k.val Φ, Submodule.subset_span ⟨k, rfl⟩⟩
  let d : K →* ℂ := (determinantWeight (charData (p 0) 0) ((m : ℂ) / 2)).comp
    (unitaryCompact ℝ (m + 1)).subtype
  let A : Module.Dual ℂ V →ₗ[ℂ] (K → ℂ) := {
    toFun := fun L k => d k * L (v k)
    map_add' := fun L L' => funext fun k => by
      change d k * (L (v k) + L' (v k)) = d k * L (v k) + d k * L' (v k)
      rw [mul_add]
    map_smul' := fun c L => funext fun k => by
      change d k * (c * L (v k)) = c * (d k * L (v k))
      rw [mul_left_comm] }
  let W := LinearMap.range A
  refine ⟨W, LinearMap.finiteDimensional_range A, ?_, ?_⟩
  · rintro _ ⟨L, rfl⟩ q
    have hq : V ≤ V.comap (ρ q.val) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨k, rfl⟩
      change ρ q.val (ρ k.val Φ) ∈ V
      rw [← Module.End.mul_apply, ← map_mul]
      exact (v (q * k)).property
    let R : V →ₗ[ℂ] V := ((ρ q.val).comp V.subtype).codRestrict V fun x => hq x.property
    refine ⟨d q • L.comp R, funext fun k => ?_⟩
    have hv : R (v k) = v (q * k) := by
      apply Subtype.ext
      change ρ q.val (ρ k.val Φ) = ρ (q.val * k.val) Φ
      rw [map_mul, Module.End.mul_apply]
    change d k * (d q * L (R (v k))) = d (q * k) * L (v (q * k))
    rw [hv, map_mul, ← mul_assoc, mul_comm (d k) (d q)]
  · refine ⟨⟨φ, hφ, S, hS, hRank, Φ, hZero, ?_⟩, rfl, rfl⟩
    intro z
    let c := charData (p 0) (z 0)
    let f := standardSection (fun i : Fin m => z i.succ) φ
    have hf : Continuous f := (standardSection_mem hφ (fun i => z i.succ)).1.1.1.continuous
    let T := {h : G | ∃ g ∈ K, rowPoint h.val g ∈ S}
    have hK : IsCompact (K : Set H) :=
      isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace K))
    have hT : IsCompact T := isCompact_support_preimage hK hS hRank
    let L := (compactTestEvaluation μ c f hf T hT).comp V.subtype
    refine ⟨L, funext fun k => ?_⟩
    change d k * (∫ h in T, f h⁻¹ * determinantWeight c (((m : ℂ) + 1) / 2) h *
      (ρ k.val Φ) (rowPoint h.val (1 : H)) ∂μ) = sectionValue μ c f Φ k.val
    have hRow (h : G) : rowPoint h.val (1 : H) * k.val.val = rowPoint h.val k.val := by
      change (h.val * lastRows (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)) * k.val.val = _
      rw [Matrix.mul_assoc]
      change h.val * lastRows ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) * k.val.val) = _
      rw [Matrix.one_mul]
      rfl
    simp only [rectangularRightRepresentation_apply, hRow]
    have hSupp (h : G) (hh : h ∉ T) :
        f h⁻¹ * determinantWeight c (((m : ℂ) + 1) / 2) h * Φ (rowPoint h.val k.val) = 0 := by
      rw [hZero _ (fun he => hh ⟨k.val, k.property, he⟩), mul_zero]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hSupp]
    unfold sectionValue innerIntegral
    change _ = determinantWeight (charData (p 0) (z 0)) ((m : ℂ) / 2) k.val * _
    rw [determinantWeight_leading_onCompact]
    rfl

end Langlands.Global.RankinSelbergGlobal.RealGodement
