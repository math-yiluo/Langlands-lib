import Langlands.Global.RankinSelberg.RealDiscreteLeviCompactProfile
import Langlands.Representation.Archimedean.RealLeftPolynomialGrowth
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! # The inner Jacquet integral for real discrete blocks -/

noncomputable section

open Complex MeasureTheory
open scoped Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealDiscreteLeviFourier

open Langlands.Archimedean Langlands.LocalFactor.Archimedean
open RealBlockRotation RealInducedBlockSlice RealInducedBlockBound
open RealLeviTorus (torusElem)
open RealInducedStandardBound (slots inClass_slots exists_hasDegree)

variable {n : ℕ}
local notation "G" => Langlands.GeneralLinear n ℝ

private theorem lowerRootElement_factor {p : ℕ} (hp : p + 1 < n) (x : ℝ) :
    lowerRootElement n p hp x =
      blockB hp (-Real.log (Real.sqrt (1 + x ^ 2))) (Real.log (Real.sqrt (1 + x ^ 2)))
        (x / Real.sqrt (1 + x ^ 2)) * blockRotation n p (Real.arctan x) := by
  let ρ := Real.sqrt (1 + x ^ 2)
  have hρ : 0 < ρ := Real.sqrt_pos.2 (by positivity)
  have hsq : ρ ^ 2 = 1 + x ^ 2 := Real.sq_sqrt (by positivity)
  apply Units.ext
  rw [Units.val_mul, blockB_eq_blockMat, blockRotation_eq_blockMat hp, blockMat_mul,
    Real.cos_arctan, Real.sin_arctan]
  change _ = blockMat hp
    (Real.exp (-Real.log ρ) * (1 / ρ) + (x / ρ) * (x / ρ))
    (Real.exp (-Real.log ρ) * (-(x / ρ)) + (x / ρ) * (1 / ρ))
    (0 * (1 / ρ) + Real.exp (Real.log ρ) * (x / ρ))
    (0 * (-(x / ρ)) + Real.exp (Real.log ρ) * (1 / ρ))
  rw [Real.exp_neg, Real.exp_log hρ]
  have h₀ : ρ⁻¹ * (1 / ρ) + (x / ρ) * (x / ρ) = 1 := by
    field_simp [hρ.ne']
    nlinarith [hsq]
  have h₁ : ρ⁻¹ * (-(x / ρ)) + (x / ρ) * (1 / ρ) = 0 := by ring
  have h₂ : ρ * (x / ρ) = x := by field_simp [hρ.ne']
  have h₃ : ρ * (1 / ρ) = 1 := by field_simp [hρ.ne']
  simp only [zero_mul, zero_add, h₀, h₁, h₂, h₃, blockMat_eq_one_add, sub_self,
    lowerRootElement_val]
  congr 1
  ext i j
  simp only [lowerRootMatrix, blockDelta, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.single_apply, ia, ib, Fin.ext_iff]
  split_ifs <;> first | (exfalso; omega) | ring

private theorem torusElem_mul_blockB {p : ℕ} (hp : p + 1 < n) (a b w : ℝ) :
    ∀ (L : List (Slot n)), (∀ t ∈ L, p + 1 < t.p ∨ t.p + 1 < p) →
      ∀ θ : Fin L.length → ℝ,
        torusElem L θ * blockB hp a b w = blockB hp a b w * torusElem L θ
  | [], _, _ => by simp [torusElem]
  | t :: L, h, θ => by
    simp only [torusElem, mul_assoc]
    rw [blockRotation_mul_blockB_comm t.hp hp (h t List.mem_cons_self).symm,
      ← mul_assoc, torusElem_mul_blockB hp a b w L (fun s hs => h s (List.mem_cons_of_mem t hs)),
      mul_assoc]

private theorem blockRadialMultiplier (α : ℂ) (k : ℕ) (x : ℝ) :
    Complex.exp (α * ↑(-Real.log (Real.sqrt (1 + x ^ 2))) +
      (α - ((k : ℂ) + 1)) * ↑(Real.log (Real.sqrt (1 + x ^ 2)))) =
      ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)⁻¹ ^ (k + 1) := by
  let ρ := Real.sqrt (1 + x ^ 2)
  have hρ : 0 < ρ := Real.sqrt_pos.2 (by positivity)
  change Complex.exp (α * ↑(-Real.log ρ) + (α - ((k : ℂ) + 1)) * ↑(Real.log ρ)) = _
  have h : α * ↑(-Real.log ρ) + (α - ((k : ℂ) + 1)) * ↑(Real.log ρ) =
      (-((k + 1 : ℕ) : ℂ)) * (Real.log ρ : ℂ) := by push_cast; ring
  rw [h, Complex.ofReal_log hρ.le, mul_comm (-((k + 1 : ℕ) : ℂ)),
    ← Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hρ.ne'),
    Complex.cpow_neg, Complex.cpow_natCast, inv_pow]

/-- The lower simple-root elements of disjoint slots, in the same order as `torusElem`. -/
def lowerBlockProduct : (L : List (Slot n)) → (Fin L.length → ℝ) → G
  | [], _ => 1
  | t :: L, x => lowerBlockProduct L (fun i => x i.succ) * lowerRootElement n t.p t.hp (x 0)

private theorem apply_lowerBlockProduct (f : G → ℂ) :
    ∀ (L : List (Slot n)), L.Pairwise Slot.Disjoint →
      (∀ t ∈ L, IsBlockCovariant t.hp t.α (t.α - (t.M + 1)) f) →
      ∀ (x : Fin L.length → ℝ) (g : G),
        f (lowerBlockProduct L x * g) =
          (∏ i : Fin L.length, ((Real.sqrt (1 + x i ^ 2) : ℝ) : ℂ)⁻¹ ^ ((L.get i).M + 1)) *
            f (torusElem L (fun i => Real.arctan (x i)) * g)
  | [], _, _, _, _ => by simp [lowerBlockProduct, torusElem]
  | t :: L, h, hCov, x, g => by
    obtain ⟨ht, hL⟩ := List.pairwise_cons.mp h
    simp only [lowerBlockProduct, torusElem, mul_assoc]
    rw [apply_lowerBlockProduct f L hL (fun s hs => hCov s (List.mem_cons_of_mem t hs)),
      lowerRootElement_factor t.hp, ← mul_assoc (torusElem L _),
      ← mul_assoc (torusElem L _) (blockB _ _ _ _), torusElem_mul_blockB t.hp _ _ _ L ht,
      mul_assoc (blockB _ _ _ _), mul_assoc (blockB _ _ _ _),
      hCov t List.mem_cons_self, blockRadialMultiplier]
    let radial (i : Fin (L.length + 1)) :=
      ((Real.sqrt (1 + x i ^ 2) : ℝ) : ℂ)⁻¹ ^ (((t :: L).get i).M + 1)
    have hrest : (∏ i : Fin L.length, radial i.succ) =
        ∏ i : Fin L.length, ((Real.sqrt (1 + x i.succ ^ 2) : ℝ) : ℂ)⁻¹ ^ ((L.get i).M + 1) := by
      rfl
    conv_rhs =>
      arg 1
      change ∏ i : Fin (L.length + 1), radial i
      rw [Fin.prod_univ_succ radial, hrest]
    simp only [radial, List.get_cons_zero, mul_assoc]
    ring

/-- The Jacquet kernel on the lower simple-root subgroups of the discrete slots, in
Lebesgue entry coordinates with independently specified frequencies. -/
def lowerBlockKernel (L : List (Slot n)) (f : G → ℂ) (g : G) (s x : Fin L.length → ℝ) : ℂ :=
  f (lowerBlockProduct L x * g) * ∏ i, Complex.exp (↑(-2 * Real.pi * x i * s i) * I)

/-- After upper triangular covariance, the inner integral on the lower simple-root
subgroups is the product angular integral of the same standard vector. -/
theorem lowerBlockKernel_eq_angularIntegrand {ds : List RealBlock}
    (f : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)) (L : List (Slot n))
    (hL : L.Pairwise Slot.Disjoint) (hs : ∀ t ∈ L, t ∈ slots ds n)
    (g : G) (s : Fin L.length → ℝ) :
    lowerBlockKernel L f.val g s =
      angularIntegrand (fun i => (L.get i).M) (compactAngularProfile L f.val g) s := by
  obtain ⟨D, hD⟩ := exists_hasDegree (RealBlockJacquet.continuous_coe f) f.2.2 (slots ds n)
  have hClass := inClass_slots f.2 hD
  funext x
  rw [lowerBlockKernel, apply_lowerBlockProduct f.val L hL (fun t ht => (hClass.2.2 _ (hs t ht)).1),
    angularIntegrand, compactAngularProfile, Finset.prod_mul_distrib]
  ring

/-- The inner Jacquet integral over the lower simple roots of any disjoint nonzero-weight
slots has the product Fourier bound on every orthogonal argument. -/
def RealDiscreteLeviInnerBoundStatement : Prop :=
  ∀ (n : ℕ) (ds : List RealBlock)
    (f : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n))
    (L : List (Slot n)), L.Pairwise Slot.Disjoint →
      (∀ t ∈ L, t ∈ slots ds n ∧ t.M ≠ 0) → ∃ C : ℝ, 0 ≤ C ∧
        ∀ (R : ℝ), (∀ g ∈ unitaryCompact ℝ n, ‖f.val g‖ ≤ R) →
          ∀ g ∈ unitaryCompact ℝ n, ∀ s : Fin L.length → ℝ,
            Integrable (lowerBlockKernel L f.val g s) ∧
              ‖∫ x, lowerBlockKernel L f.val g s x‖ ≤
                C * R * ∏ i, |s i| ^ (((L.get i).M : ℝ) / 2)

theorem realDiscreteLeviInnerBound : RealDiscreteLeviInnerBoundStatement := by
  intro n ds f L hL hs
  obtain ⟨C, hC, hB⟩ := realDiscreteLeviCompactProfile n ds f L hL hs
  refine ⟨C, hC, fun R hR g hg s => ?_⟩
  have hEq := lowerBlockKernel_eq_angularIntegrand f L hL (fun t ht => (hs t ht).1) g s
  exact hEq ▸ hB R hR g hg s

end Langlands.Global.RankinSelbergGlobal.RealDiscreteLeviFourier
