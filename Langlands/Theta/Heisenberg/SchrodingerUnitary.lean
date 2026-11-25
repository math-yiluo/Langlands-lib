import Langlands.Theta.Heisenberg.Schrodinger
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The `L²` inner product of the Schrödinger model

GKT §1.3.1 (Lemma 1.30 and Theorem 1.31, p. 36: the Heisenberg representation is unitarizable),
in the Schrödinger model, where the invariant Hermitian form is the `L²` inner product of a Haar
measure.

* `schwartzBruhatInner μ`: `(f, g) ↦ ∫ conj(f) g dμ` on Schwartz–Bruhat functions, a sesquilinear
  form, for a measure `μ` finite on compact sets; `schwartzBruhatInner_self`: `⟨f, f⟩ = ∫ ‖f‖²`;
  `schwartzBruhatInner_map`: a linear map preserving `∫ ‖f‖²` preserves the form (polarization).
* `HeisenbergGroup.schrodingerSB_lintegral_enorm_sq`, `HeisenbergGroup.schrodingerSB_inner`: for a
  translation-invariant measure and a character of modulus one, the operators of the Schrödinger
  model preserve `∫ ‖φ‖²` and the inner product.
-/

noncomputable section

open MeasureTheory

namespace Langlands.Theta

open HarmonicAnalysis

section L2

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ]

/-- The product `conj(f) g` of two Schwartz–Bruhat functions is integrable. -/
theorem integrable_conj_mul_schwartzBruhat (f g : SchwartzBruhat X) :
    Integrable (fun x => (starRingEnd ℂ) ((f : X → ℂ) x) * (g : X → ℂ) x) μ := by
  have hc : Continuous fun x => (starRingEnd ℂ) ((f : X → ℂ) x) * (g : X → ℂ) x :=
    (Complex.continuous_conj.comp f.2.1.continuous).mul g.2.1.continuous
  exact hc.integrable_of_hasCompactSupport g.2.2.mul_left

/-- The `L²` inner product `⟨f, g⟩ = ∫ conj(f) g dμ` of Schwartz–Bruhat functions, a sesquilinear
form (conjugate-linear in `f`). -/
def schwartzBruhatInner : SchwartzBruhat X →ₗ⋆[ℂ] SchwartzBruhat X →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ)
    (fun f g => ∫ x, (starRingEnd ℂ) ((f : X → ℂ) x) * (g : X → ℂ) x ∂μ)
    (fun f f' g => by
      simp only [Submodule.coe_add, Pi.add_apply, map_add, add_mul]
      exact integral_add (integrable_conj_mul_schwartzBruhat μ f g)
        (integrable_conj_mul_schwartzBruhat μ f' g))
    (fun c f g => by
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc]
      exact integral_const_mul _ _)
    (fun f g g' => by
      simp only [Submodule.coe_add, Pi.add_apply, mul_add]
      exact integral_add (integrable_conj_mul_schwartzBruhat μ f g)
        (integrable_conj_mul_schwartzBruhat μ f g'))
    (fun c f g => by
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
        mul_left_comm _ c]
      exact integral_const_mul _ _)

theorem schwartzBruhatInner_apply (f g : SchwartzBruhat X) :
    schwartzBruhatInner μ f g = ∫ x, (starRingEnd ℂ) ((f : X → ℂ) x) * (g : X → ℂ) x ∂μ := rfl

/-- `⟨f, f⟩ = ∫ ‖f‖²`, read from the `L²` norm `∫⁻ ‖f‖ₑ²`. -/
theorem schwartzBruhatInner_self (f : SchwartzBruhat X) :
    schwartzBruhatInner μ f f = ((∫⁻ x, ‖(f : X → ℂ) x‖ₑ ^ 2 ∂μ).toReal : ℂ) := by
  rw [schwartzBruhatInner_apply]
  have e : ∀ x, (starRingEnd ℂ) ((f : X → ℂ) x) * (f : X → ℂ) x = ((‖(f : X → ℂ) x‖ ^ 2 : ℝ) : ℂ) :=
    fun x => by rw [Complex.conj_mul']; push_cast; ring
  simp only [e]
  rw [integral_complex_ofReal, integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun x => by positivity)]
  · congr 2
    refine lintegral_congr fun x => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  · exact ((continuous_norm.comp f.2.1.continuous).pow 2).aestronglyMeasurable

/-- **Polarization**: a linear map preserving `∫ ‖f‖²` preserves the `L²` inner product. -/
theorem schwartzBruhatInner_map (T : SchwartzBruhat X →ₗ[ℂ] SchwartzBruhat X)
    (hT : ∀ f, ∫⁻ x, ‖(T f : X → ℂ) x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖(f : X → ℂ) x‖ₑ ^ 2 ∂μ)
    (f g : SchwartzBruhat X) :
    schwartzBruhatInner μ (T f) (T g) = schwartzBruhatInner μ f g := by
  set B := schwartzBruhatInner μ
  have hN : ∀ u, B (T u) (T u) = B u u := fun u => by
    rw [schwartzBruhatInner_self, schwartzBruhatInner_self, hT]
  have pol : ∀ u v, 4 * B u v = (B (u + v) (u + v) - B (u - v) (u - v)) -
      Complex.I * (B (u + Complex.I • v) (u + Complex.I • v) -
        B (u - Complex.I • v) (u - Complex.I • v)) := fun u v => by
    simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply, map_smulₛₗ,
      LinearMap.smul_apply, smul_eq_mul, Complex.conj_I, RingHom.id_apply]
    ring_nf
    rw [Complex.I_sq]
    ring
  have h4 : (4 : ℂ) ≠ 0 := by norm_num
  apply mul_left_cancel₀ h4
  rw [pol, pol, ← map_add, ← map_sub, ← map_smul, ← map_add, ← map_sub, hN, hN, hN, hN]

end L2

end Langlands.Theta

namespace Langlands.HeisenbergGroup

open MeasureTheory HarmonicAnalysis

variable {R : Type*} [CommRing R] [Invertible (2 : R)] [TopologicalSpace R]
  [NonarchimedeanAddGroup R] {X Y : Type*} [AddCommGroup X] [Module R X] [AddCommGroup Y]
  [Module R Y] [TopologicalSpace X] [IsTopologicalAddGroup X] [MeasurableSpace X] [BorelSpace X]
  {ψ : AddChar R ℂ} {β : X →ₗ[R] Y →ₗ[R] R}

/-- **The Schrödinger model is unitary** for a translation-invariant measure on `X` and a character
of modulus one: its operators preserve `∫ ‖φ‖²`. -/
theorem schrodingerSB_lintegral_enorm_sq (hψ : Continuous ψ) (hβ : ∀ y, Continuous fun x => β x y)
    (hψ1 : ∀ t, ‖ψ t‖ = 1) (μ : Measure X) [μ.IsAddLeftInvariant]
    (g : HeisenbergGroup (polarizedForm β)) (φ : SchwartzBruhat X) :
    ∫⁻ x, ‖(schrodingerSB hψ hβ g φ : X → ℂ) x‖ₑ ^ 2 ∂μ =
      ∫⁻ x, ‖(φ : X → ℂ) x‖ₑ ^ 2 ∂μ := by
  have e : ∀ x, ‖(schrodingerSB hψ hβ g φ : X → ℂ) x‖ₑ = ‖(φ : X → ℂ) (g.vec.1 + x)‖ₑ := fun x => by
    rw [schrodingerSB_apply, schrodinger_apply, Pi.smul_apply, schrodingerFun_apply, smul_eq_mul,
      enorm_mul, enorm_mul, add_comm x]
    simp only [← ofReal_norm, hψ1, ENNReal.ofReal_one, one_mul]
  simp only [e]
  exact lintegral_add_left_eq_self (fun x => ‖(φ : X → ℂ) x‖ₑ ^ 2) g.vec.1

/-- The operators of the Schrödinger model preserve the `L²` inner product. -/
theorem schrodingerSB_inner (hψ : Continuous ψ) (hβ : ∀ y, Continuous fun x => β x y)
    (hψ1 : ∀ t, ‖ψ t‖ = 1) (μ : Measure X) [μ.IsAddLeftInvariant] [IsFiniteMeasureOnCompacts μ]
    (g : HeisenbergGroup (polarizedForm β)) (f f' : SchwartzBruhat X) :
    Theta.schwartzBruhatInner μ (schrodingerSB hψ hβ g f) (schrodingerSB hψ hβ g f') =
      Theta.schwartzBruhatInner μ f f' :=
  Theta.schwartzBruhatInner_map μ (schrodingerSB hψ hβ g)
    (schrodingerSB_lintegral_enorm_sq hψ hβ hψ1 μ g) f f'

end Langlands.HeisenbergGroup
