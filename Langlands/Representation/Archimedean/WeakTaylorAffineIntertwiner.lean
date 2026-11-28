import Langlands.Representation.Archimedean.RealBlockMultiplierAnalytic
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Taylor coefficients of an affine intertwining identity -/

noncomputable section

open Filter
open scoped Topology
open Langlands.Archimedean.RealBlockMultiplierAnalytic

set_option autoImplicit false

namespace Langlands.Archimedean.WeakTaylorAffineIntertwiner

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

private def scalarCoefficient (d : ℕ) (f : ℂ → ℂ) : ℂ :=
  iteratedDeriv d f 0 / (d.factorial : ℂ)

private theorem scalarCoefficient_add (d : ℕ) {f g : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    scalarCoefficient d (fun z => f z + g z) =
      scalarCoefficient d f + scalarCoefficient d g := by
  rw [scalarCoefficient, iteratedDeriv_fun_add hf.contDiffAt hg.contDiffAt, add_div]
  rfl

private theorem scalarCoefficient_mul_parameter (d : ℕ) {f : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) :
    scalarCoefficient d (fun z => z * f z) =
      if d = 0 then 0 else scalarCoefficient (d - 1) f := by
  cases d with
  | zero => simp [scalarCoefficient]
  | succ d =>
    have hid : AnalyticAt ℂ (fun z : ℂ => z) 0 := analyticAt_id
    have hsum :
        (∑ i ∈ Finset.range (d + 1 + 1),
          ((d + 1).choose i : ℂ) * (if i = 1 then 1 else 0) *
            iteratedDeriv (d + 1 - i) f 0) =
          ((d : ℂ) + 1) * iteratedDeriv d f 0 := by
      rw [Finset.sum_eq_single 1 (by intro i _ hi; simp [hi]) (by simp)]
      simp
    have hpos : ((d : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero d
    have hfactorial : (d.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero d
    simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    rw [scalarCoefficient, iteratedDeriv_fun_mul hid.contDiffAt hf.contDiffAt]
    simp only [iteratedDeriv_fun_id_zero]
    rw [hsum, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, scalarCoefficient]
    field_simp

/-- The maps `B d` give the factorial-normalized derivatives of `T` after
testing with each algebraic dual functional. -/
def HasWeakTaylorCoefficients (T : ℂ → V →ₗ[ℂ] W) (B : ℕ → V →ₗ[ℂ] W) : Prop :=
  ∀ (d : ℕ) (v : V) (ℓ : Module.Dual ℂ W),
    ℓ (B d v) = iteratedDeriv d (fun z => ℓ (T z v)) 0 / (d.factorial : ℂ)

/-- A weakly analytic intertwiner of two affine operator families intertwines
their coefficient actions degree by degree. -/
def WeakTaylorAffineIntertwinerStatement : Prop :=
  ∀ (T : ℂ → V →ₗ[ℂ] W) (B : ℕ → V →ₗ[ℂ] W)
    (D N : V →ₗ[ℂ] V) (D' N' : W →ₗ[ℂ] W),
    (∀ v, IsWeaklyAnalyticAt (fun z => T z v) 0) → HasWeakTaylorCoefficients T B →
    (∀ v, ∀ᶠ z in 𝓝 (0 : ℂ), T z (D v + z • N v) = D' (T z v) + z • N' (T z v)) →
    ∀ (d : ℕ) (v : V),
      B d (D v) + (if d = 0 then 0 else B (d - 1) (N v)) =
        D' (B d v) + (if d = 0 then 0 else N' (B (d - 1) v))

theorem weakTaylorAffineIntertwiner : WeakTaylorAffineIntertwinerStatement (V := V) (W := W) := by
  intro T B D N D' N' hT hB h d v
  apply Module.eval_apply_injective ℂ
  ext ℓ
  change ℓ _ = ℓ _
  have h₀ : (fun z => ℓ (T z (D v)) + z * ℓ (T z (N v))) =ᶠ[𝓝 0]
      fun z => (ℓ.comp D') (T z v) + z * (ℓ.comp N') (T z v) := by
    filter_upwards [h v] with z hz
    simpa only [map_add, map_smul, smul_eq_mul, LinearMap.comp_apply] using congrArg ℓ hz
  have hc : scalarCoefficient d _ = scalarCoefficient d _ :=
    congrArg (· / (d.factorial : ℂ)) (h₀.iteratedDeriv_eq d)
  have hz (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) : AnalyticAt ℂ (fun z => z * f z) 0 :=
    analyticAt_id.mul hf
  rw [scalarCoefficient_add d (hT (D v) ℓ) (hz _ (hT (N v) ℓ)),
    scalarCoefficient_add d (hT v (ℓ.comp D')) (hz _ (hT v (ℓ.comp N'))),
    scalarCoefficient_mul_parameter d (hT (N v) ℓ),
    scalarCoefficient_mul_parameter d (hT v (ℓ.comp N'))] at hc
  change ∀ (d : ℕ) (v : V) (ℓ : Module.Dual ℂ W),
    ℓ (B d v) = scalarCoefficient d (fun z => ℓ (T z v)) at hB
  rw [← hB d (D v) ℓ, ← hB (d - 1) (N v) ℓ,
    ← hB d v (ℓ.comp D'), ← hB (d - 1) v (ℓ.comp N')] at hc
  simpa only [map_add, apply_ite ℓ, map_zero, LinearMap.comp_apply] using hc

end Langlands.Archimedean.WeakTaylorAffineIntertwiner
