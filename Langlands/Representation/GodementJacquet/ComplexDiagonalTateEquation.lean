import Langlands.Representation.GodementJacquet.ComplexDiagonalTateStrip
import Mathlib.Analysis.Meromorphic.Order

/-! # Meromorphic product Tate equations for complex diagonal integrals -/

noncomputable section

open Set Filter
open scoped Topology BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet

open Langlands.LocalFactor

variable {ι : Type*} [Fintype ι]
local notation "Z" => ι → ℂ
local notation "R" => ι → ℝ

private def InCommonStrip (z : ℂ) : Prop := 0 < z.re ∧ z.re < 1

private def AvoidsMellinPoles (z : ℂ) : Prop :=
  (∀ j : ℕ, 2 * z + (j : ℂ) ≠ 0) ∧ ∀ j : ℕ, 2 * (1 - z) + (j : ℂ) ≠ 0

private theorem InCommonStrip.avoidsMellinPoles {z : ℂ} (hz : InCommonStrip z) :
    AvoidsMellinPoles z := by
  constructor <;> intro j he <;> have hre := congrArg Complex.re he
  all_goals
    simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
      zero_mul, sub_zero, Complex.natCast_re, Complex.sub_re, Complex.one_re, Complex.zero_re] at hre
    linarith [hz.1, hz.2, show (0 : ℝ) ≤ (j : ℝ) by positivity]

private theorem avoidsMellinPoles_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) :
    AvoidsMellinPoles z := by
  constructor <;> intro j he <;> have him := congrArg Complex.im he
  all_goals
    simp only [Complex.add_im, Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat,
      add_zero, Complex.natCast_im, Complex.sub_im, Complex.one_im,
      zero_sub, Complex.zero_im] at him
    exact hz (by linarith)

private theorem meromorphic_germ_eq {f g : ℂ → ℂ} (hf : Meromorphic f) (hg : Meromorphic g)
    {z₀ : ℂ} (he : f =ᶠ[𝓝 z₀] g) (z : ℂ) : f =ᶠ[𝓝[≠] z] g := by
  have h₀ : meromorphicOrderAt (f - g) z₀ = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    filter_upwards [he.filter_mono nhdsWithin_le_nhds] with w hw
    exact sub_eq_zero.mpr hw
  have hz := (hf.sub hg).meromorphicOn.meromorphicOrderAt_eq_top_of_isPreconnected
    isPreconnected_univ (mem_univ z₀) (mem_univ z) h₀
  filter_upwards [meromorphicOrderAt_eq_top_iff.mp hz] with w hw
  exact sub_eq_zero.mp hw

private theorem differentiable_inv_complexDiagonalGamma_affine (m : ι → ℤ) (c : R) (b : Z) :
    Differentiable ℂ
      (fun z : ℂ => (complexDiagonalGamma m (fun i => (c i : ℂ) * z + b i))⁻¹) := by
  simp only [complexDiagonalGamma, ← Finset.prod_inv_distrib]
  exact Differentiable.fun_finsetProd fun i _ =>
    Complex.differentiable_Gammaℂ_inv.comp (by fun_prop)

private theorem meromorphic_normalizedDiagonalZeta_affine (Φ : SchwartzMap Z ℂ)
    (m : ι → ℤ) (c : R) (b : Z) :
    Meromorphic (fun z : ℂ => complexDiagonalZeta 1 Φ m (fun i => (c i : ℂ) * z + b i) /
      complexDiagonalGamma m (fun i => (c i : ℂ) * z + b i)) := by
  simp only [div_eq_mul_inv]
  exact (meromorphic_complexDiagonalZeta_affine 1 Φ m c b).mul
    (fun z => ((differentiable_inv_complexDiagonalGamma_affine m c b).analyticAt z).meromorphicAt)

private theorem continuousAt_normalizedDiagonalZeta_affine (Φ : SchwartzMap Z ℂ)
    (m : ι → ℤ) (c : R) (b : Z) {z : ℂ}
    (hz : ∀ (i : ι) (j : ℕ), 2 * ((c i : ℂ) * z + b i) + (j : ℂ) ≠ 0) :
    ContinuousAt (fun w : ℂ => complexDiagonalZeta 1 Φ m (fun i => (c i : ℂ) * w + b i) /
      complexDiagonalGamma m (fun i => (c i : ℂ) * w + b i)) z := by
  simp only [div_eq_mul_inv]
  exact (analyticAt_complexDiagonalZeta_affine 1 Φ m c b hz).continuousAt.mul
    ((differentiable_inv_complexDiagonalGamma_affine m c b).continuous.continuousAt)

omit [Fintype ι] in
private theorem reflect_affine (c : R) (b : Z) (z : ℂ) :
    (1 - (fun i => (c i : ℂ) * z + b i) : Z) = fun i => ((-c i : ℝ) : ℂ) * z + (1 - b i) := by
  funext i
  simp only [Pi.sub_apply, Pi.one_apply, Complex.ofReal_neg]
  ring

private theorem meromorphic_extend_product_strip (F H : Z → ℂ)
    (hF : ∀ (c : R) (b : Z), Meromorphic (fun z => F (fun i => (c i : ℂ) * z + b i)))
    (hH : ∀ (c : R) (b : Z), Meromorphic (fun z => H (fun i => (c i : ℂ) * z + b i)))
    (hcF : ∀ (c : R) (b : Z) (z : ℂ), (∀ i, AvoidsMellinPoles ((c i : ℂ) * z + b i)) →
      ContinuousAt (fun w => F (fun i => (c i : ℂ) * w + b i)) z)
    (hcH : ∀ (c : R) (b : Z) (z : ℂ), (∀ i, AvoidsMellinPoles ((c i : ℂ) * z + b i)) →
      ContinuousAt (fun w => H (fun i => (c i : ℂ) * w + b i)) z)
    (hstrip : ∀ u : Z, (∀ i, InCommonStrip (u i)) → F u = H u) :
    ∀ u : Z, (∀ i, AvoidsMellinPoles (u i)) → F u = H u := by
  classical
  suffices ∀ (S : Finset ι) (u : Z), (∀ j, AvoidsMellinPoles (u j)) →
      (∀ j, j ∉ S → InCommonStrip (u j)) → F u = H u from
    fun u hu => this Finset.univ u hu (by simp)
  intro S
  induction S using Finset.induction_on with
  | empty =>
      exact fun u _ hu => hstrip u fun i => hu i (Finset.notMem_empty i)
  | @insert i S hi ih =>
      intro u hu hstrip'
      let c (j : ι) : ℝ := if j = i then 1 else 0
      let b (j : ι) : ℂ := if j = i then 0 else u j
      let v (w : ℂ) (j : ι) : ℂ := (c j : ℂ) * w + b j
      have heq (w : ℂ) : v w = Function.update u i w := by
        funext j
        rcases eq_or_ne j i with rfl | hj
        · simp [v, c, b]
        · simp [v, c, b, hj]
      have hp (w : ℂ) (hw : InCommonStrip w) : F (v w) = H (v w) := by
        apply ih (v w)
        · intro j
          rcases eq_or_ne j i with rfl | hj
          · simpa [heq] using hw.avoidsMellinPoles
          · simpa only [heq, Function.update_of_ne hj] using hu j
        · intro j hj
          rcases eq_or_ne j i with rfl | hji
          · simpa [heq] using hw
          · have hnot : j ∉ insert i S := by simpa [hji] using hj
            simpa only [heq, Function.update_of_ne hji] using hstrip' j hnot
      have h₀ : InCommonStrip (1 / 2 : ℂ) := by
        simp only [InCommonStrip, Complex.div_ofNat_re, Complex.one_re]
        norm_num
      have hopen : IsOpen {w : ℂ | InCommonStrip w} :=
        (isOpen_lt continuous_const Complex.continuous_re).inter
          (isOpen_lt Complex.continuous_re continuous_const)
      have hh₀ : ∀ᶠ w : ℂ in 𝓝 (1 / 2 : ℂ), InCommonStrip w := hopen.mem_nhds h₀
      have hh : (fun w => F (v w)) =ᶠ[𝓝 (1 / 2 : ℂ)] fun w => H (v w) := hh₀.mono hp
      have hr : v (u i) = u := by rw [heq, Function.update_eq_self]
      have ha (j : ι) : AvoidsMellinPoles (v (u i) j) := by rw [hr]; exact hu j
      have hg := meromorphic_germ_eq (hF c b) (hH c b) hh (u i)
      have h := (hcF c b (u i) ha).eventuallyEq_nhds_iff_eventuallyEq_nhdsNE (hcH c b (u i) ha)
      have huv : F (v (u i)) = H (v (u i)) := (h.mp hg).eq_of_nhds
      rwa [hr] at huv

/-- The normalized product Tate equation away from the possible radial Mellin poles. -/
theorem complexDiagonalTateEquation_regular (hTate : ComplexArchimedeanTateStatement)
    (Φ Φf : SchwartzMap Z ℂ) (hΦ : (Φf : Z → ℂ) = complexCoordinateFourier 1 Φ)
    (m : ι → ℤ) (u : Z)
    (h₀ : ∀ (i : ι) (j : ℕ), 2 * u i + (j : ℂ) ≠ 0)
    (h₁ : ∀ (i : ι) (j : ℕ), 2 * (1 - u i) + (j : ℂ) ≠ 0) :
    complexDiagonalZeta 1 Φf (-m) (1 - u) / complexDiagonalGamma (-m) (1 - u) =
      complexDiagonalStandardEpsilon m * (complexDiagonalZeta 1 Φ m u / complexDiagonalGamma m u) := by
  let L (v : Z) := complexDiagonalZeta 1 Φf (-m) (1 - v) / complexDiagonalGamma (-m) (1 - v)
  let H (v : Z) := complexDiagonalStandardEpsilon m *
    (complexDiagonalZeta 1 Φ m v / complexDiagonalGamma m v)
  change L u = H u
  apply meromorphic_extend_product_strip L H _ _ _ _ _ u (fun i => ⟨h₀ i, h₁ i⟩)
  · intro c b
    simp only [L, reflect_affine]
    exact meromorphic_normalizedDiagonalZeta_affine Φf (-m) (fun i => -c i) (fun i => 1 - b i)
  · intro c b z
    exact (MeromorphicAt.const _ z).mul (meromorphic_normalizedDiagonalZeta_affine Φ m c b z)
  · intro c b z hz
    simp only [L, reflect_affine]
    refine continuousAt_normalizedDiagonalZeta_affine Φf (-m) (fun i => -c i) (fun i => 1 - b i) ?_
    intro i j
    have he := congrFun (reflect_affine c b z) i
    rw [← he]
    exact (hz i).2 j
  · intro c b z hz
    exact continuousAt_const.mul (continuousAt_normalizedDiagonalZeta_affine Φ m c b
      (fun i => (hz i).1))
  · exact fun v hv => complexDiagonalTateEquation_strip hTate Φ Φf hΦ m
      (fun i => (hv i).1) (fun i => (hv i).2)

/-- The normalized diagonal functional equation as an equality of punctured
germs along the common spectral variable, for arbitrary inducing exponents. -/
theorem complexDiagonalTateEquation (hTate : ComplexArchimedeanTateStatement)
    (Φ Φf : SchwartzMap Z ℂ) (hΦ : (Φf : Z → ℂ) = complexCoordinateFourier 1 Φ)
    (m : ι → ℤ) (t : Z) (s₀ : ℂ) :
    (fun s : ℂ => complexDiagonalZeta 1 Φf (-m) (fun i => 1 - (s + t i)) /
      complexDiagonalGamma (-m) (fun i => 1 - (s + t i))) =ᶠ[𝓝[≠] s₀]
    (fun s : ℂ => complexDiagonalStandardEpsilon m *
      (complexDiagonalZeta 1 Φ m (fun i => s + t i) / complexDiagonalGamma m (fun i => s + t i))) := by
  let L (s : ℂ) := complexDiagonalZeta 1 Φf (-m) (fun i => 1 - (s + t i)) /
    complexDiagonalGamma (-m) (fun i => 1 - (s + t i))
  let H (s : ℂ) := complexDiagonalStandardEpsilon m *
    (complexDiagonalZeta 1 Φ m (fun i => s + t i) / complexDiagonalGamma m (fun i => s + t i))
  have hL : Meromorphic L := by
    have he (s : ℂ) (i : ι) : 1 - (s + t i) = ((-1 : ℝ) : ℂ) * s + (1 - t i) := by
      push_cast
      ring
    simp only [L, he]
    exact meromorphic_normalizedDiagonalZeta_affine Φf (-m) (fun _ => -1) (fun i => 1 - t i)
  have hH : Meromorphic H := by
    intro z
    apply (MeromorphicAt.const _ z).mul
    simpa only [Complex.ofReal_one, one_mul] using
      meromorphic_normalizedDiagonalZeta_affine Φ m (fun _ => 1) t z
  obtain ⟨a, ha⟩ := Finite.exists_le (fun i => -(t i).im)
  let z := ((a + 1 : ℝ) : ℂ) * Complex.I
  have hz (i : ι) : 0 < (z + t i).im := by
    simp only [z, Complex.add_im, Complex.mul_im, Complex.I_im, Complex.I_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_one, zero_mul, add_zero]
    linarith [ha i]
  have hv : ∀ᶠ w : ℂ in 𝓝 z, ∀ i, 0 < (w + t i).im := by
    apply eventually_all.2
    intro i
    exact (isOpen_lt continuous_const (show Continuous (fun w : ℂ => (w + t i).im) by fun_prop)).mem_nhds
      (hz i)
  apply meromorphic_germ_eq hL hH (z₀ := z) _ s₀
  filter_upwards [hv] with w hw
  have ha' (i : ι) := avoidsMellinPoles_of_im_ne_zero (hw i).ne'
  exact complexDiagonalTateEquation_regular hTate Φ Φf hΦ m (fun i => w + t i)
    (fun i => (ha' i).1) (fun i => (ha' i).2)

end Langlands.GodementJacquet
