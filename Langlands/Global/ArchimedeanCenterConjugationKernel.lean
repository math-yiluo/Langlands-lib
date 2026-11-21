import Langlands.Global.ArchimedeanEnvelopingInvariantCenter
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.MeanValue

/-! # An open kernel for archimedean conjugation on the enveloping center -/

noncomputable section

universe u

open Filter NumberField
open scoped Classical Matrix.Norms.Operator Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000

namespace Langlands.Global.ArchimedeanGL

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

local notation "G" => InfiniteAdelicGL F n
local notation "M" => ArchimedeanMatrix F n
local notation "Z" => EnvelopingCenter F n
local notation "A" => EnvelopingAlgebra F n
local notation "e" => archimedeanGLCoordinates F n

private theorem coordinates_realLieExponentialCurve (Y : RealLieAlgebra F n) (t : ℝ) :
    (e (realLieExponentialCurve F n Y t)).val =
      NormedSpace.exp (t • realLieAlgebraToMatrix F n Y) := by
  rw [realLieExponentialCurve, ContinuousMulEquiv.apply_symm_apply]
  rfl

private theorem realLieExponentialCurve_add (Y : RealLieAlgebra F n) (s t : ℝ) :
    realLieExponentialCurve F n Y (s + t) =
      realLieExponentialCurve F n Y s * realLieExponentialCurve F n Y t := by
  apply (e).injective
  apply Units.ext
  rw [map_mul, Units.val_mul, coordinates_realLieExponentialCurve,
    coordinates_realLieExponentialCurve, coordinates_realLieExponentialCurve, add_smul]
  exact NormedSpace.exp_add_of_commute (𝔸 := M)
    (((Commute.refl (realLieAlgebraToMatrix F n Y)).smul_left s).smul_right t)

/-- Conjugation by a real exponential is pointwise trivial on the
enveloping-algebra center. -/
theorem centerConjugation_realLieExponentialCurve
    (Y : RealLieAlgebra F n) (t : ℝ) (z : Z) :
    centerConjugation F n (realLieExponentialCurve F n Y t) z = z := by
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff ℂ _).mp
  intro l
  let f (s : ℝ) := l (envelopingConjugation F n (realLieExponentialCurve F n Y s) z.val)
  have hf (s : ℝ) : HasDerivAt f 0 s := by
    let w := centerConjugation F n (realLieExponentialCurve F n Y s) z
    let a := envelopingGenerator F n (complexify F n Y)
    have hc : a * w.val = w.val * a := Subalgebra.mem_center_iff.mp w.property a
    have hd := exponentialCurve_enveloping_deriv F n Y w.val l
    change HasDerivAt _ (l (a * w.val - w.val * a)) 0 at hd
    rw [hc, sub_self, map_zero] at hd
    have h := hd.scomp_of_eq s ((hasDerivAt_id s).sub_const s) (sub_self s).symm
    change HasDerivAt (fun r => l (envelopingConjugation F n
        (realLieExponentialCurve F n Y (r - s)) w.val)) ((1 : ℝ) • (0 : ℂ)) s at h
    have heq : (fun r => l (envelopingConjugation F n
        (realLieExponentialCurve F n Y (r - s)) w.val)) = f := by
      funext r
      change l (envelopingConjugation F n (realLieExponentialCurve F n Y (r - s))
        (envelopingConjugation F n (realLieExponentialCurve F n Y s) z.val)) =
        l (envelopingConjugation F n (realLieExponentialCurve F n Y r) z.val)
      rw [← sub_add_cancel r s, realLieExponentialCurve_add, envelopingConjugation_mul]
      simp only [AlgEquiv.trans_apply, sub_add_cancel]
    simpa only [heq, smul_zero] using h
  have hf' : ∀ s, deriv f s = 0 := fun s => (hf s).deriv
  have h := is_const_of_deriv_eq_zero (fun s => (hf s).differentiableAt) hf' t 0
  have hz : f 0 = l z.val := by
    simp only [f, realLieExponentialCurve_zero, envelopingConjugation_one]
    rfl
  rw [map_sub, sub_eq_zero]
  exact h.trans hz

/-- The adjoint action on the center as an ordinary group homomorphism. -/
def centerConjugationHom : G →* (Z ≃ₐ[ℂ] Z) where
  toFun := centerConjugation F n
  map_one' := centerConjugation_one F n
  map_mul' := centerConjugation_mul F n

/-- A single open subgroup fixes every element of the enveloping center. -/
theorem isOpen_ker_centerConjugationHom :
    IsOpen ((centerConjugationHom F n).ker : Set G) := by
  apply (centerConjugationHom F n).ker.isOpen_of_mem_nhds (g := (1 : G))
  have hmap : map NormedSpace.exp (𝓝 (0 : M)) = 𝓝 (NormedSpace.exp (0 : M)) :=
    (hasStrictFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := M)).map_nhds_eq_of_surj
      (LinearMap.range_eq_top.mpr fun x => ⟨x, rfl⟩)
  rw [NormedSpace.exp_zero] at hmap
  have hr : Set.range (NormedSpace.exp : M → M) ∈ 𝓝 (1 : M) := by
    rw [← hmap]
    exact Filter.mem_map.mpr (by simp)
  let c : G → M := fun g => (e g).val
  have hc : Continuous c := Units.continuous_val.comp (e).continuous
  have hc1 : c 1 = 1 := by simp [c]
  have hh : c ⁻¹' Set.range (NormedSpace.exp : M → M) ∈ 𝓝 (1 : G) :=
    hc.continuousAt.preimage_mem_nhds (hc1.symm ▸ hr)
  refine Filter.mem_of_superset hh ?_
  rintro g ⟨Y, hY⟩
  let X := (realLieAlgebraToMatrix F n).symm Y
  have hg : realLieExponentialCurve F n X 1 = g := by
    apply (e).injective
    apply Units.ext
    rw [coordinates_realLieExponentialCurve, one_smul]
    change NormedSpace.exp (realLieAlgebraToMatrix F n X) = c g
    rw [LinearEquiv.apply_symm_apply]
    exact hY
  rw [← hg]
  change centerConjugation F n (realLieExponentialCurve F n X 1) = AlgEquiv.refl
  apply AlgEquiv.ext
  intro z
  exact centerConjugation_realLieExponentialCurve F n X 1 z

end Langlands.Global.ArchimedeanGL
