import Langlands.LinearAlgebra.GMFamilyRootWalls
import Langlands.Analysis.SmoothIntervalParameterIntegral
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Complex.RealDeriv

/-! # Smooth division by the distinct hyperplanes of a family -/

noncomputable section

open Classical MeasureTheory Set
open scoped ContDiff

namespace Langlands.GMFamily

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The linear factor for an imaginary parameter, with real coordinates. -/
def imaginaryFactor (l : V →L[ℝ] ℝ) (x : V) : ℂ := Complex.I * (l x : ℂ)

@[simp]
theorem imaginaryFactor_eq_zero {l : V →L[ℝ] ℝ} {x : V} : imaginaryFactor l x = 0 ↔ l x = 0 := by
  simp [imaginaryFactor, Complex.I_ne_zero]

theorem contDiff_imaginaryFactor (l : V →L[ℝ] ℝ) : ContDiff ℝ ∞ (imaginaryFactor l) :=
  contDiff_const.mul (Complex.ofRealCLM.contDiff.comp l.contDiff)

/-- The product of the imaginary linear factors indexed by a finite set. -/
def imaginaryProduct {ι : Type*} (s : Finset ι) (l : ι → V →L[ℝ] ℝ) (x : V) : ℂ :=
  ∏ i ∈ s, imaginaryFactor (l i) x

theorem contDiff_imaginaryProduct {ι : Type*} (s : Finset ι) (l : ι → V →L[ℝ] ℝ) :
    ContDiff ℝ ∞ (imaginaryProduct s l) :=
  contDiff_prod (fun i _ => contDiff_imaginaryFactor (l i))

private theorem exists_factor_of_zero_on_hyperplane (l : V →L[ℝ] ℝ) (hl : l ≠ 0)
    {g : V → ℂ} (hg : ContDiff ℝ ∞ g) (hz : ∀ x, l x = 0 → g x = 0) :
    ∃ u : V → ℂ, ContDiff ℝ ∞ u ∧ ∀ x, g x = imaginaryFactor l x * u x := by
  have hne : ∃ v, l v ≠ 0 := by
    by_contra! hn
    exact hl (ContinuousLinearMap.ext hn)
  obtain ⟨v, hv⟩ := hne
  let e : V := (l v)⁻¹ • v
  have he : l e = 1 := by simp [e, map_smul, smul_eq_mul, hv]
  let p (x : V) := x - l x • e
  have hp : ∀ x, l (p x) = 0 := by intro x; simp [p, map_smul, he]
  let path (x : V) (t : ℝ) := p x + (t * l x) • e
  have hpath : ContDiff ℝ ∞ (fun z : V × ℝ => path z.1 z.2) :=
    (contDiff_fst.sub (l.contDiff.comp contDiff_fst |>.smul contDiff_const)).add
      ((contDiff_snd.mul (l.contDiff.comp contDiff_fst)).smul contDiff_const)
  let D (z : V × ℝ) := fderiv ℝ g (path z.1 z.2) e
  have hD : ContDiff ℝ ∞ D :=
    ((hg.fderiv_right (m := ∞) (by simp)).comp hpath).clm_apply contDiff_const
  let U (x : V) := ∫ t in (0 : ℝ)..1, D (x, t)
  have hU : ContDiff ℝ ∞ U := Langlands.Analysis.contDiff_intervalIntegral_of_joint hD zero_le_one
  refine ⟨fun x => Complex.I⁻¹ * U x, contDiff_const.mul hU, fun x => ?_⟩
  have hderiv (t : ℝ) : HasDerivAt (fun s => g (path x s)) (l x • D (x, t)) t := by
    have hp' : HasDerivAt (path x) (l x • e) t := by
      simpa only [path, id_eq, one_mul] using
        (((hasDerivAt_id t).mul_const (l x)).smul_const e).const_add (p x)
    have hd : DifferentiableAt ℝ g (path x t) := hg.contDiffAt.differentiableAt (by simp)
    have he : l x • D (x, t) = fderiv ℝ g (path x t) (l x • e) := (map_smul _ _ _).symm
    rw [he]
    exact hd.hasFDerivAt.comp_hasDerivAt t hp'
  have hcont₀ : Continuous (fun t : ℝ => D (x, t)) :=
    hD.continuous.comp (continuous_const.prodMk continuous_id)
  have hcont : Continuous (fun t : ℝ => l x • D (x, t)) :=
    (show Continuous (fun _ : ℝ => l x) from continuous_const).smul hcont₀
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 0) (b := 1) (fun t _ => hderiv t) (hcont.intervalIntegrable 0 1)
  have hends : path x 1 = x ∧ path x 0 = p x := by simp [path, p]
  rw [hends.1, hends.2, hz _ (hp x), sub_zero, intervalIntegral.integral_smul] at hFTC
  calc
    g x = (l x : ℂ) * U x := by simpa only [Complex.real_smul] using hFTC.symm
    _ = imaginaryFactor l x * (Complex.I⁻¹ * U x) := by
      rw [imaginaryFactor]
      field_simp [Complex.I_ne_zero]

/-- On a given hyperplane the complement of the other hyperplanes is dense, provided each
other form is nonzero somewhere on the given hyperplane. -/
theorem vanishes_on_wall_of_vanishes_off_others {ι : Type*} (s : Finset ι)
    (l : ι → V →L[ℝ] ℝ) (b : V →L[ℝ] ℝ)
    (hn : ∀ j ∈ s, ∃ x, b x = 0 ∧ l j x ≠ 0) {g : V → ℂ} (hg : Continuous g)
    (hz : ∀ x, b x = 0 → (∀ j ∈ s, l j x ≠ 0) → g x = 0) :
    ∀ x, b x = 0 → g x = 0 := by
  let W := b.ker
  let l' (j : ι) := (l j).comp W.subtypeL
  have hd : Dense {x : W | ∀ j ∈ s, l' j x ≠ 0} := dense_nonzero_forms s l' fun j hj he => by
    obtain ⟨y, hy, hjy⟩ := hn j hj
    exact hjy (DFunLike.congr_fun he ⟨y, hy⟩)
  have hclosed : IsClosed {x : W | g (x : V) = 0} :=
    isClosed_eq (hg.comp continuous_subtype_val) continuous_const
  intro x hx
  have hsub : {y : W | ∀ j ∈ s, l' j y ≠ 0} ⊆ {y : W | g (y : V) = 0} :=
    fun y hy => hz y y.property hy
  exact closure_minimal hsub hclosed (hd ⟨x, hx⟩)

/-- A smooth function vanishing on each of finitely many distinct hyperplanes is smoothly
 divisible by the product of their linear factors. -/
theorem smooth_factor_hyperplanes {ι : Type*} (s : Finset ι) (l : ι → V →L[ℝ] ℝ)
    (hn : ∀ i ∈ s, l i ≠ 0)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∃ x, l i x = 0 ∧ l j x ≠ 0)
    {g : V → ℂ} (hg : ContDiff ℝ ∞ g) (hz : ∀ i ∈ s, ∀ x, l i x = 0 → g x = 0) :
    ∃ u : V → ℂ, ContDiff ℝ ∞ u ∧ ∀ x, g x = (∏ i ∈ s, imaginaryFactor (l i) x) * u x := by
  induction s using Finset.induction_on generalizing g with
  | empty => exact ⟨g, hg, by simp⟩
  | @insert i s hi ih =>
    have hi' : i ∈ insert i s := Finset.mem_insert_self ..
    have hsub : s ⊆ insert i s := Finset.subset_insert i s
    obtain ⟨g', hg', hmul⟩ := exists_factor_of_zero_on_hyperplane (l i) (hn i hi') hg (hz i hi')
    have hz' (j : ι) (hj : j ∈ s) : ∀ x, l j x = 0 → g' x = 0 := by
      apply vanishes_on_wall_of_vanishes_off_others {i} l (l j) _ hg'.continuous
      · intro x hx hn'
        have he : imaginaryFactor (l i) x * g' x = 0 := (hmul x).symm.trans (hz j (hsub hj) x hx)
        exact (mul_eq_zero.mp he).resolve_left (fun h => hn' i (by simp) (imaginaryFactor_eq_zero.mp h))
      · intro k hk
        have he : k = i := Finset.mem_singleton.mp hk
        subst k
        exact hsep j (hsub hj) i hi' (fun he => hi (he ▸ hj))
    obtain ⟨u, hu, hfac⟩ := ih (fun j hj => hn j (hsub hj))
      (fun j hj k hk => hsep j (hsub hj) k (hsub hk)) hg' hz'
    refine ⟨u, hu, fun x => ?_⟩
    rw [hmul, hfac, Finset.prod_insert hi, mul_assoc]

end Langlands.GMFamily
