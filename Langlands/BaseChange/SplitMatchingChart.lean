import Langlands.BaseChange.SplitMatchingHaar
import Mathlib.MeasureTheory.Group.Prod

/-! Ordered products and a measure-preserving chart for the split cycle. -/

noncomputable section

open MeasureTheory

namespace Langlands.BaseChange

universe u

section Tuples

variable {G : Type u} [TopologicalSpace G]

/-- Separate the first entry of a tuple from its tail. -/
def splitFinHead (l : ℕ) : (Fin (l + 1) → G) ≃ₜ G × (Fin l → G) where
  toEquiv := (Fin.consEquiv (fun _ : Fin (l + 1) => G)).symm
  continuous_toFun :=
    (continuous_apply 0).prodMk (continuous_pi fun i => continuous_apply i.succ)
  continuous_invFun := continuous_pi fun i => by
    induction i using Fin.cases with
    | zero => simpa using (continuous_fst : Continuous fun p : G × (Fin l → G) => p.1)
    | succ i => simpa [Function.comp_def] using
        ((continuous_apply i).comp continuous_snd :
          Continuous fun p : G × (Fin l → G) => p.2 i)

@[simp] theorem splitFinHead_apply (l : ℕ) (x : Fin (l + 1) → G) :
    splitFinHead l x = (x 0, Fin.tail x) := rfl

@[simp] theorem splitFinHead_symm_apply (l : ℕ) (p : G × (Fin l → G)) :
    (splitFinHead l).symm p = Fin.cons p.1 p.2 := rfl

theorem splitFinHead_measurePreserving [MeasurableSpace G]
    (μ : Measure G) [SigmaFinite μ] (l : ℕ) :
    MeasurePreserving (splitFinHead l) (Measure.pi (fun _ : Fin (l + 1) => μ))
      (μ.prod (Measure.pi (fun _ : Fin l => μ))) :=
  measurePreserving_piFinSuccAbove (fun _ : Fin (l + 1) => μ) 0

theorem splitOrderedProduct_snoc {M : Type*} [Monoid M] {l : ℕ}
    (w : Fin l → M) (a : M) :
    (List.ofFn (@Fin.snoc l (fun _ => M) w a)).prod = (List.ofFn w).prod * a := by
  rw [List.ofFn_succ', List.prod_concat]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

theorem splitOrderedProduct_init_last {M : Type*} [Monoid M] {l : ℕ}
    (w : Fin (l + 1) → M) :
    (List.ofFn w).prod = (List.ofFn (Fin.init w)).prod * w (Fin.last l) := by
  conv_lhs => rw [← Fin.snoc_init_self (q := w), splitOrderedProduct_snoc]

variable [Group G] [IsTopologicalGroup G]

/-- Change the second entry while holding the first entry and the tail fixed. -/
private def splitCycleStep (d : G) (l : ℕ) : G × (G × (Fin l → G)) ≃ₜ G × (G × (Fin l → G)) where
  toFun p := (p.1, (p.1⁻¹ * d * p.2.1, p.2.2))
  invFun p := (p.1, (d⁻¹ * p.1 * p.2.1, p.2.2))
  left_inv p := by simp [mul_assoc]
  right_inv p := by simp [mul_assoc]
  continuous_toFun := continuous_fst.prodMk
    ((continuous_fst.inv.mul continuous_const |>.mul
      (continuous_fst.comp continuous_snd)).prodMk (continuous_snd.comp continuous_snd))
  continuous_invFun := continuous_fst.prodMk
    ((continuous_const.mul continuous_fst |>.mul
      (continuous_fst.comp continuous_snd)).prodMk (continuous_snd.comp continuous_snd))

private theorem splitCycleStep_measurePreserving [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G]
    (μ : Measure G) [SigmaFinite μ] [μ.IsMulLeftInvariant] (d : G) (l : ℕ) :
    MeasurePreserving (splitCycleStep d l)
      (μ.prod (μ.prod (Measure.pi (fun _ : Fin l => μ))))
      (μ.prod (μ.prod (Measure.pi (fun _ : Fin l => μ)))) := by
  refine (MeasurePreserving.id μ).skew_product
    (μc := μ.prod (Measure.pi (fun _ : Fin l => μ)))
    (μd := μ.prod (Measure.pi (fun _ : Fin l => μ)))
    (g := fun x p => (x⁻¹ * d * p.1, p.2)) ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact ((continuous_fst.inv.mul continuous_const |>.mul
      (continuous_fst.comp continuous_snd)).measurable).prodMk
      (measurable_snd.comp measurable_snd)
  · exact ((measurePreserving_mul_left μ (x⁻¹ * d)).prod
      (MeasurePreserving.id (Measure.pi (fun _ : Fin l => μ)))).map_eq

/-- Keep the first entry and record `xᵢ⁻¹ dᵢ xᵢ₊₁` for all nonfinal indices. -/
def splitCycleChart : {l : ℕ} → (Fin (l + 1) → G) → (Fin (l + 1) → G) ≃ₜ G × (Fin l → G)
  | 0, _ => splitFinHead 0
  | l + 1, d =>
    ((splitFinHead (l + 1)).trans ((Homeomorph.refl G).prodCongr
      (splitCycleChart (Fin.tail d)))).trans ((splitCycleStep (d 0) l).trans
        ((Homeomorph.refl G).prodCongr (splitFinHead l).symm))

@[simp] theorem splitCycleChart_fst {l : ℕ} (d x : Fin (l + 1) → G) :
    (splitCycleChart d x).1 = x 0 := by
  cases l <;> rfl

theorem splitCycleChart_snd {l : ℕ} (d x : Fin (l + 1) → G) (i : Fin l) :
    (splitCycleChart d x).2 i = (x i.castSucc)⁻¹ * d i.castSucc * x i.succ := by
  induction l with
  | zero => exact Fin.elim0 i
  | succ l ih =>
    induction i using Fin.cases with
    | zero =>
      change @Fin.cons l (fun _ => G)
        ((x 0)⁻¹ * d 0 * (splitCycleChart (Fin.tail d) (Fin.tail x)).1)
        (splitCycleChart (Fin.tail d) (Fin.tail x)).2 0 = _
      rw [Fin.cons_zero, splitCycleChart_fst]
      rfl
    | succ i =>
      change @Fin.cons l (fun _ => G)
        ((x 0)⁻¹ * d 0 * (splitCycleChart (Fin.tail d) (Fin.tail x)).1)
        (splitCycleChart (Fin.tail d) (Fin.tail x)).2 i.succ = _
      rw [Fin.cons_succ, ih]
      rfl

theorem splitCycleChart_measurePreserving [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G]
    (μ : Measure G) [SigmaFinite μ] [μ.IsMulLeftInvariant] {l : ℕ} (d : Fin (l + 1) → G) :
    MeasurePreserving (splitCycleChart d) (Measure.pi (fun _ : Fin (l + 1) => μ))
      (μ.prod (Measure.pi (fun _ : Fin l => μ))) := by
  induction l with
  | zero => exact splitFinHead_measurePreserving μ 0
  | succ l ih =>
    have htail := (MeasurePreserving.id μ).prod (ih (Fin.tail d))
    have hcons := (splitFinHead_measurePreserving μ l).symm
      (splitFinHead l).toMeasurableEquiv
    exact ((MeasurePreserving.id μ).prod hcons).comp
      ((splitCycleStep_measurePreserving μ (d 0) l).comp
        (htail.comp (splitFinHead_measurePreserving μ (l + 1))))

end Tuples

section Norm

open Fin.NatCast

variable {F : Type u} [Field F] [TopologicalSpace F] {n l : ℕ}

local notation "G" => GeneralLinear n F
local notation "GE" => GeneralLinear n (Fin (l + 1) → F)
local notation "κ" => splitGLCoordinates F n (l + 1)
local notation "σ" => splitCyclicShift F (l + 1)

theorem splitGLCoordinates_shift_pow (δ : GE) (k : ℕ) (i : Fin (l + 1)) :
    κ (entrywiseAut (σ ^ k) n δ) i = κ δ ((finRotate (l + 1) ^ k) i) := by
  simp only [splitGLCoordinates_apply]
  ext a b
  exact splitCyclicShift_pow_apply F (l + 1) k (δ a b) i

private theorem splitGLCoordinates_norm_prefix (δ : GE) (k : ℕ) (i : Fin (l + 1)) :
    κ (cyclicNorm σ k δ) i =
      (List.ofFn fun j : Fin k => κ δ ((finRotate (l + 1) ^ (j : ℕ)) i)).prod := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [cyclicNorm_succ, map_mul, Pi.mul_apply, ih, splitGLCoordinates_shift_pow,
      List.ofFn_succ', List.prod_concat]
    rfl

/-- The zeroth norm coordinate is the ordered product around the cycle. -/
theorem splitGLCoordinates_norm_zero (δ : GE) :
    κ (cyclicNorm σ (l + 1) δ) 0 = (List.ofFn (κ δ)).prod := by
  rw [splitGLCoordinates_norm_prefix]
  have hcast (j : Fin (l + 1)) : ((j : ℕ) : Fin (l + 1)) = j :=
    Fin.ext (Nat.mod_eq_of_lt j.isLt)
  simp only [finRotate_succ_pow_apply, zero_add, hcast]

/-- Every element is a norm in the split algebra. -/
theorem isNorm_splitCyclicShift (γ : G) : IsNorm σ (l + 1) γ := by
  let d : Fin (l + 1) → G := fun i => if i = 0 then γ else 1
  let δ : GE := (κ).symm d
  have hd : κ δ = d := (κ).apply_symm_apply d
  have hperiod := (isCyclicAlgebra_splitCyclicShift F l).pow_eq_one
  have hz : κ (cyclicNorm σ (l + 1) δ) 0 = γ := by
    rw [splitGLCoordinates_norm_zero, hd, List.ofFn_succ]
    simp [d]
  have hi (i : Fin (l + 1)) : κ (cyclicNorm σ (l + 1) δ) i = γ := by
    induction i using Fin.induction with
    | zero => exact hz
    | succ i ih =>
      rw [← show finRotate (l + 1) i.castSucc = i.succ from finRotate_of_lt i.isLt,
        ← splitGLCoordinates_shift, entrywiseAut_cyclicNorm, hperiod, entrywiseAut_one_apply,
        map_mul, map_mul, map_inv, Pi.mul_apply, Pi.mul_apply, Pi.inv_apply, ih, hd]
      by_cases h : i.castSucc = 0 <;> simp [d, h]
  refine ⟨δ, 1, ?_⟩
  simp only [inv_one, one_mul, mul_one]
  apply (κ).injective
  funext i
  rw [hi, splitGLCoordinates_baseChange]

end Norm

end Langlands.BaseChange
