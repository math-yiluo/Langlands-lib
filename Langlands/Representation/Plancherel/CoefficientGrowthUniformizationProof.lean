import Langlands.Representation.Plancherel.CoefficientGrowthUniformizationStatement
import Langlands.Representation.Smooth.Contragredient.FiniteLengthProof
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RepresentationTheory.Subrepresentation

/-! # Uniform coefficient degrees from finite generation -/

noncomputable section

namespace Langlands.Plancherel

open scoped MonoidAlgebra

universe uG uV

private theorem exists_top_of_exhaustive_chain
    {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [Module.Finite R M]
    (N : ℕ →o Submodule R M) (hcover : ∀ x : M, ∃ d, x ∈ N d) :
    ∃ d, N d = ⊤ := by
  have hsup : iSup N = ⊤ := by
    apply top_unique
    intro x _
    exact (Submodule.mem_iSup_of_chain N x).mpr (hcover x)
  obtain ⟨d, hd⟩ := (Module.Finite.fg_top (R := R) (M := M)).stabilizes_of_iSup_eq N hsup
  exact ⟨d, hd.symm⟩

variable {G : Type uG}

private def powerBound (H : G → ℝ) (d : ℕ) (f : G → ℂ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ g, ‖f g‖ ≤ c * H g ^ d

private theorem powerBound_zero (H : G → ℝ) (hH : ∀ g, 1 ≤ H g) (d : ℕ) :
    powerBound H d (fun _ => 0) := by
  refine ⟨1, zero_lt_one, fun g => ?_⟩
  simpa using pow_nonneg (le_trans zero_le_one (hH g)) d

private theorem powerBound_add {H : G → ℝ} {d : ℕ} {f k : G → ℂ}
    (hf : powerBound H d f) (hk : powerBound H d k) :
    powerBound H d (fun g => f g + k g) := by
  obtain ⟨c, hc, hf⟩ := hf
  obtain ⟨b, hb, hk⟩ := hk
  refine ⟨c + b, add_pos hc hb, fun g => ?_⟩
  calc
    ‖f g + k g‖ ≤ ‖f g‖ + ‖k g‖ := norm_add_le _ _
    _ ≤ c * H g ^ d + b * H g ^ d := add_le_add (hf g) (hk g)
    _ = (c + b) * H g ^ d := (add_mul _ _ _).symm

private theorem powerBound_smul {H : G → ℝ} {d : ℕ} {f : G → ℂ}
    (hf : powerBound H d f) (a : ℂ) (hH : ∀ g, 1 ≤ H g) :
    powerBound H d (fun g => a * f g) := by
  obtain ⟨c, hc, hf⟩ := hf
  refine ⟨(‖a‖ + 1) * c, mul_pos (by positivity) hc, fun g => ?_⟩
  calc
    ‖a * f g‖ = ‖a‖ * ‖f g‖ := norm_mul _ _
    _ ≤ ‖a‖ * (c * H g ^ d) := mul_le_mul_of_nonneg_left (hf g) (norm_nonneg _)
    _ ≤ (‖a‖ + 1) * (c * H g ^ d) :=
      mul_le_mul_of_nonneg_right (by linarith)
        (mul_nonneg hc.le (pow_nonneg (le_trans zero_le_one (hH g)) d))
    _ = ((‖a‖ + 1) * c) * H g ^ d := (mul_assoc _ _ _).symm

private theorem powerBound_mono {H : G → ℝ} {d e : ℕ} {f : G → ℂ}
    (hH : ∀ g, 1 ≤ H g) (hde : d ≤ e) (hf : powerBound H d f) :
    powerBound H e f := by
  obtain ⟨c, hc, hf⟩ := hf
  exact ⟨c, hc, fun g => (hf g).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (hH g) hde) hc.le)⟩

variable [Group G]

private theorem powerBound_left {H : G → ℝ} {d : ℕ} {f : G → ℂ}
    (hH : ∀ g, 1 ≤ H g) (hmul : ∀ g h, H (g * h) ≤ H g * H h)
    (hf : powerBound H d f) (h : G) :
    powerBound H d (fun g => f (h * g)) := by
  obtain ⟨c, hc, hf⟩ := hf
  refine ⟨c * H h ^ d, mul_pos hc (pow_pos (lt_of_lt_of_le zero_lt_one (hH h)) d),
    fun g => ?_⟩
  calc
    ‖f (h * g)‖ ≤ c * H (h * g) ^ d := hf _
    _ ≤ c * (H h * H g) ^ d :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (le_trans zero_le_one (hH _)) (hmul h g) d) hc.le
    _ = (c * H h ^ d) * H g ^ d := by rw [mul_pow, mul_assoc]

private theorem powerBound_right {H : G → ℝ} {d : ℕ} {f : G → ℂ}
    (hH : ∀ g, 1 ≤ H g) (hmul : ∀ g h, H (g * h) ≤ H g * H h)
    (hf : powerBound H d f) (h : G) :
    powerBound H d (fun g => f (g * h)) := by
  obtain ⟨c, hc, hf⟩ := hf
  refine ⟨c * H h ^ d, mul_pos hc (pow_pos (lt_of_lt_of_le zero_lt_one (hH h)) d),
    fun g => ?_⟩
  calc
    ‖f (g * h)‖ ≤ c * H (g * h) ^ d := hf _
    _ ≤ c * (H g * H h) ^ d :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (le_trans zero_le_one (hH _)) (hmul g h) d) hc.le
    _ = (c * H h ^ d) * H g ^ d := by rw [mul_pow]; ring

variable [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

private def dualDegreeSubrepresentation (ρ : Representation ℂ G V)
    (H : G → ℝ) (hH : ∀ g, 1 ≤ H g)
    (hmul : ∀ g h, H (g * h) ≤ H g * H h) (v : V) (d : ℕ) :
    Subrepresentation (smoothContragredient ρ) where
  toSubmodule :=
    { carrier := {φ | powerBound H d (fun g => (φ : Module.Dual ℂ V) (ρ g v))}
      zero_mem' := by
        exact powerBound_zero H hH d
      add_mem' := by
        intro φ ψ hφ hψ
        exact powerBound_add hφ hψ
      smul_mem' := by
        intro a φ hφ
        exact powerBound_smul hφ a hH }
  apply_mem_toSubmodule h φ hφ := by
    change powerBound H d (fun g => (φ : Module.Dual ℂ V) (ρ h⁻¹ (ρ g v)))
    simpa only [map_mul, Module.End.mul_apply] using powerBound_left hH hmul hφ h⁻¹

private def vectorDegreeSubrepresentation (ρ : Representation ℂ G V)
    (H : G → ℝ) (hH : ∀ g, 1 ≤ H g)
    (hmul : ∀ g h, H (g * h) ≤ H g * H h) (d : ℕ) :
    Subrepresentation ρ where
  toSubmodule :=
    { carrier := {v | ∀ φ : SmoothDual ρ,
        powerBound H d (fun g => (φ : Module.Dual ℂ V) (ρ g v))}
      zero_mem' := by
        intro φ
        simpa only [map_zero] using powerBound_zero H hH d
      add_mem' := by
        intro v w hv hw φ
        simpa only [map_add] using powerBound_add (hv φ) (hw φ)
      smul_mem' := by
        intro a v hv φ
        simpa only [map_smul, smul_eq_mul] using powerBound_smul (hv φ) a hH }
  apply_mem_toSubmodule h v hv := by
    intro φ
    simpa only [map_mul, Module.End.mul_apply] using powerBound_right hH hmul (hv φ) h

private theorem uniform_powerBound (ρ : Representation ℂ G V)
    (H : G → ℝ) (hH : ∀ g, 1 ≤ H g)
    (hmul : ∀ g h, H (g * h) ≤ H g * H h)
    [Module.Finite ℂ[G] ρ.asModule]
    [Module.Finite ℂ[G] (smoothContragredient ρ).asModule]
    (hcoeff : ∀ (v : V) (φ : SmoothDual ρ),
      ∃ d, powerBound H d (fun g => (φ : Module.Dual ℂ V) (ρ g v))) :
    ∃ d, ∀ (v : V) (φ : SmoothDual ρ),
      powerBound H d (fun g => (φ : Module.Dual ℂ V) (ρ g v)) := by
  have hvector : ∀ v : V, ∃ d, ∀ φ : SmoothDual ρ,
      powerBound H d (fun g => (φ : Module.Dual ℂ V) (ρ g v)) := by
    intro v
    let N : ℕ →o Submodule ℂ[G] (smoothContragredient ρ).asModule :=
      { toFun := fun d => (dualDegreeSubrepresentation ρ H hH hmul v d).asSubmodule
        monotone' := by
          intro d e hde φ hφ
          exact powerBound_mono hH hde hφ }
    have hcover : ∀ φ : (smoothContragredient ρ).asModule, ∃ d, φ ∈ N d := by
      intro φ
      exact hcoeff v ((smoothContragredient ρ).asModuleEquiv φ)
    obtain ⟨d, hd⟩ := exists_top_of_exhaustive_chain N hcover
    refine ⟨d, fun φ => ?_⟩
    have hφ : (smoothContragredient ρ).asModuleEquiv.symm φ ∈ N d := by
      rw [hd]
      trivial
    exact hφ
  let N : ℕ →o Submodule ℂ[G] ρ.asModule :=
    { toFun := fun d => (vectorDegreeSubrepresentation ρ H hH hmul d).asSubmodule
      monotone' := by
        intro d e hde v hv φ
        exact powerBound_mono hH hde (hv φ) }
  have hcover : ∀ v : ρ.asModule, ∃ d, v ∈ N d := by
    intro v
    exact hvector (ρ.asModuleEquiv v)
  obtain ⟨d, hd⟩ := exists_top_of_exhaustive_chain N hcover
  refine ⟨d, fun v => ?_⟩
  have hv : ρ.asModuleEquiv.symm v ∈ N d := by
    rw [hd]
    trivial
  exact hv

/-- Finite length and admissibility make a coefficientwise degree bound uniform
in both the vector and the smooth functional. -/
theorem finiteLengthCoefficientGrowthUniformization :
    FiniteLengthCoefficientGrowthUniformizationStatement.{uG, uV} := by
  intro G _ _ _ hcof H hH hmul π hπ hfinite hcoeff
  have : IsNoetherian ℂ[G] π.representation.asModule :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hfinite).1
  have hdual := π.contragredient_hasFiniteLength hcof hπ hfinite
  have : IsNoetherian ℂ[G] (smoothContragredient π.representation).asModule :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hdual).1
  exact uniform_powerBound π.representation H hH hmul hcoeff

end Langlands.Plancherel
