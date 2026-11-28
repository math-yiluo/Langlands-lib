import Langlands.Analysis.HolomorphicContDiff
import Langlands.Global.AdelicCompactSpectralDisplacement
import Langlands.Global.AdelicOrthantHolomorphicIdentification
import Langlands.Global.AdelicVaryingConeFourierBoundary
import Langlands.LinearAlgebra.GMFamilyConeIntegrals

/-! # The finite cone Fourier boundary on a relative spectral plane -/

noncomputable section

open Filter MeasureTheory Set
open scoped ContDiff ENNReal NNReal Topology

set_option autoImplicit false

namespace Langlands.Global

open ImaginaryAxis Langlands.Analysis

instance coordinateSpectralMeasure_isAddHaarMeasure
    (ι : Type*) [Fintype ι] : (coordinateSpectralMeasure ι).IsAddHaarMeasure := by
  unfold coordinateSpectralMeasure
  refine Measure.IsAddHaarMeasure.smul _
    (pow_ne_zero _ (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)) ?_
  exact ENNReal.pow_ne_top (by simp [Real.pi_pos])

/-- The signed orthant Fourier boundary for given spectral coordinates and Haar factors. -/
def HasRelativeConeFourierBoundary {η L : Type*} [Fintype η] [Fintype L]
    {ι : L → Type*} [∀ l, Fintype (ι l)] (μ : Measure (η → ℝ))
    (e : ∀ l, (η → ℝ) ≃L[ℝ] (ι l → ℝ)) (c : L → ℝ≥0) : Prop :=
  ∀ {n : ℕ} (b d ξ : ∀ l, ι l → ℝ) (P : ∀ l, MvPolynomial (ι l) ℂ)
      (z : ∀ l, (Fin n → ℂ) → ι l → ℂ) (a : L → (Fin n → ℂ) → ℂ)
      (representative : (Fin n → ℂ) → ℂ) (U : Set (Fin n → ℂ)) (S : Set (Fin n → ℝ))
      (γ : ℝ × (η → ℝ) → (Fin n → ℂ)),
      IsOpen U → range imaginarySlice ⊆ U → Dense S →
      DifferentiableOn ℂ representative U →
      (∀ l, DifferentiableOn ℂ (a l) U) →
      (∀ l i, DifferentiableOn ℂ (fun s => z l s i) U) →
      (∀ x ∈ S, (∀ l i, z l (imaginarySlice x) i ≠ 0) ∧
        representative (imaginarySlice x) =
          ∑ l, a l (imaginarySlice x) * regularizedOrthantTerm (b l) (P l) (z l (imaginarySlice x))) →
      ContDiff ℝ ∞ γ → (∀ x, γ (0, x) ∈ range imaginarySlice) →
      (∀ l i, d l i ≠ 0) →
      (∀ t x l, z l (γ (t, x)) = displacedOrthantParameter (d l) t (e l x - ξ l)) →
      ∀ f : (η → ℝ) → ℂ, ContDiff ℝ ∞ f → HasCompactSupport f →
        let w (l : L) (y : ι l → ℝ) := f ((e l).symm y) * a l (γ (0, (e l).symm y))
        (∀ l, ContDiff ℝ ∞ (w l) ∧ HasCompactSupport (w l)) ∧
        Integrable (fun x => f x * representative (γ (0, x))) μ ∧
        (∫ x, f x * representative (γ (0, x)) ∂μ) =
          ∑ l, ((c l : ℝ) : ℂ) * orthantSign (d l) *
            ∫ u in translatedOrientedOrthant (d l) (b l),
              orthantPolynomialTest (coordinateSpectralMeasure (ι l))
                (fun y => w l (y + ξ l)) (P l) u

/-- A holomorphic finite cone sum, restricted to a displaced relative spectral plane, has
the signed orthant Fourier boundary after testing against a compactly supported smooth function.
The Haar factors are determined before the vertices, frequencies and weights are chosen. -/
def RelativeConeFourierBoundaryStatement : Prop :=
  ∀ {η L : Type*} [Fintype η] [Fintype L] {ι : L → Type*} [∀ l, Fintype (ι l)]
    (μ : Measure (η → ℝ)) [μ.IsAddHaarMeasure]
    (e : ∀ l, (η → ℝ) ≃L[ℝ] (ι l → ℝ)),
    ∃ c : L → ℝ≥0, (∀ l, 0 < c l) ∧ HasRelativeConeFourierBoundary μ e c

/-- The spectral Haar factor of each label is the scalar of the unshifted chart's
pushforward relative to the coordinate spectral measure. -/
theorem relativeConeFourierBoundary_withHaar {η L : Type*} [Fintype η] [Fintype L]
    {ι : L → Type*} [∀ l, Fintype (ι l)] (μ : Measure (η → ℝ)) [μ.IsAddHaarMeasure]
    (e : ∀ l, (η → ℝ) ≃L[ℝ] (ι l → ℝ)) :
    ∃ c : L → ℝ≥0, (∀ l, Measure.map (e l) μ = c l • coordinateSpectralMeasure (ι l)) ∧
      (∀ l, 0 < c l) ∧ HasRelativeConeFourierBoundary μ e c := by
  classical
  have hHaar (l : L) : (Measure.map (e l) μ).IsAddHaarMeasure := (e l).isAddHaarMeasure_map μ
  let c (l : L) := Measure.addHaarScalarFactor (Measure.map (e l) μ) (coordinateSpectralMeasure (ι l))
  have hUnshifted (l : L) : Measure.map (e l) μ = c l • coordinateSpectralMeasure (ι l) := by
    let := hHaar l
    exact Measure.isAddLeftInvariant_eq_smul _ _
  refine ⟨c, hUnshifted, fun l => ?_, ?_⟩
  · let := hHaar l
    exact Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _
  intro n b d ξ P z a representative U S γ hU haxis hS hω ha hz hmatch hγ hγaxis hd hchart f hf hfs w
  obtain ⟨W, hW, hWaxis, hWU, hident⟩ :=
    finiteOrthantHolomorphicIdentification b P z a representative U S hU haxis hS hω ha hz hmatch
  let V := γ ⁻¹' W
  have hV : IsOpen V := hW.preimage hγ.continuous
  have hVzero : {0} ×ˢ tsupport f ⊆ V := by
    rintro ⟨t, x⟩ ⟨ht, _⟩
    have ht' : t = 0 := mem_singleton_iff.mp ht
    subst t
    exact hWaxis (hγaxis x)
  have hωlocal : ContinuousOn (fun p => representative (γ p)) V :=
    hω.continuousOn.comp hγ.continuous.continuousOn (fun _ hp => hWU hp)
  have haLocal (l : L) : ContDiffOn ℝ ∞ (fun p => a l (γ p)) V :=
    ((contDiffOn_of_differentiableOn hU (ha l)).restrict_scalars ℝ).comp
      hγ.contDiffOn (fun _ hp => hWU hp)
  obtain ⟨hIntω, hLimω⟩ :=
    compactSpectralIntegral_tendsto (μ := μ) hV hf.continuous hfs hωlocal hVzero
  choose g hgs hge _ hgSmooth using fun l =>
    compactSpectralDisplacement f (fun p => a l (γ p)) V hV hfs hVzero
  have hg (l : L) : ContDiff ℝ ∞ (g l) := hgSmooth l hf (haLocal l)
  have hw (l : L) : ContDiff ℝ ∞ (w l) ∧ HasCompactSupport (w l) := by
    have hEq : w l = fun y => g l (0, (e l).symm y) :=
      funext fun y => ((hge l).self_of_nhds ((e l).symm y)).symm
    rw [hEq]
    refine ⟨(hg l).comp (contDiff_const.prodMk (e l).symm.contDiff), ?_⟩
    have hs := hfs.image (e l).continuous
    refine hs.of_isClosed_subset isClosed_closure (closure_minimal ?_ hs.isClosed)
    intro y hy
    by_contra h
    exact hy (hgs l 0 _ (fun hx => h ⟨_, hx, (e l).apply_symm_apply y⟩))
  refine ⟨hw, hIntω, ?_⟩
  let E (l : L) := (e l).toHomeomorph.trans (Homeomorph.subRight (ξ l))
  have hE (l : L) (x : η → ℝ) : E l x = e l x - ξ l := rfl
  have hEinv (l : L) (y : ι l → ℝ) : (E l).symm y = (e l).symm (y + ξ l) := by
    apply (E l).injective
    rw [Homeomorph.apply_symm_apply, hE, (e l).apply_symm_apply, add_sub_cancel_right]
  have hMap (l : L) : Measure.map (E l) μ = c l • coordinateSpectralMeasure (ι l) := by
    let := hHaar l
    calc
      _ = Measure.map (fun y : ι l → ℝ => -ξ l + y) (Measure.map (e l) μ) := by
        rw [Measure.map_map (measurable_const_add _) (e l).continuous.measurable]
        congr 1
        funext x
        rw [hE, Function.comp_apply, sub_eq_add_neg, add_comm]
      _ = Measure.map (e l) μ := (measurePreserving_add_left _ (-ξ l)).map_eq
      _ = _ := hUnshifted l
  let A (l : L) (p : ℝ × (ι l → ℝ)) := g l (p.1, (E l).symm p.2)
  have hA (l : L) : ContDiff ℝ ∞ (A l) := by
    simp only [A, hEinv]
    change ContDiff ℝ ∞
      (g l ∘ fun p : ℝ × (ι l → ℝ) => (p.1, (e l).symm (p.2 + ξ l)))
    exact (hg l).comp
      (contDiff_fst.prodMk ((e l).symm.contDiff.comp (contDiff_snd.add contDiff_const)))
  let S' (l : L) := E l '' tsupport f
  have hS' (l : L) : IsCompact (S' l) := hfs.image (E l).continuous
  have hAs (l : L) (t : ℝ) (y : ι l → ℝ) (hy : y ∉ S' l) : A l (t, y) = 0 :=
    hgs l t _ fun hx => hy ⟨_, hx, (E l).apply_symm_apply y⟩
  have hAzero (l : L) : (fun y => A l (0, y)) = fun y => w l (y + ξ l) := by
    funext y
    simp only [A, hEinv, (hge l).self_of_nhds, w]
  let K (l : L) (t : ℝ) (y : ι l → ℝ) :=
    regularizedOrthantTerm (b l) (P l) (displacedOrthantParameter (d l) t y)
  let G (l : L) (t : ℝ) (y : ι l → ℝ) := K l t y * A l (t, y)
  let J (l : L) (t : ℝ) (x : η → ℝ) := K l t (E l x) * g l (t, x)
  have hJE (l : L) (t : ℝ) (x : η → ℝ) : G l t (E l x) = J l t x := by
    simp only [G, J, A, Homeomorph.symm_apply_apply]
  have hInt (l : L) {t : ℝ} (ht : 0 < t) : Integrable (J l t) μ := by
    have hAInt : Integrable (fun y => A l (t, y)) (coordinateSpectralMeasure (ι l)) :=
      (SchwartzCompactFamilies.ofCompactSupport (fun y => A l (t, y))
        ((hA l).comp (contDiff_const.prodMk contDiff_id)) (S' l) (hS' l) (hAs l t)).integrable
    have hG := (regularizedOrthantTerm_integrable_integral (d l) (b l) (hd l) (P l) hAInt ht).1
    have hG' : Integrable (G l t) (Measure.map (E l) μ) := by
      rw [hMap]
      exact hG.smul_measure_nnreal
    have h := (integrable_map_equiv (E l).toMeasurableEquiv (G l t)).mp hG'
    exact h.congr (ae_of_all _ (hJE l t))
  have hChange (l : L) (t : ℝ) :
      (∫ x, J l t x ∂μ) = ((c l : ℝ) : ℂ) *
        ∫ y, G l t y ∂coordinateSpectralMeasure (ι l) := by
    calc
      _ = ∫ x, G l t (E l x) ∂μ := by simp_rw [hJE]
      _ = ∫ y, G l t y ∂Measure.map (E l) μ :=
        (integral_map_equiv (E l).toMeasurableEquiv (G l t)).symm
      _ = _ := by rw [hMap, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  have hTerm (l : L) := regularizedOrthantFourierBoundary_compactFamily
    (d l) (b l) (hd l) (P l) (A l) (hA l) (S' l) (hS' l) (hAs l)
  have hLim (l : L) :
      Tendsto (fun t : ℝ => ∫ x, J l t x ∂μ) (𝓝[>] 0)
        (𝓝 (((c l : ℝ) : ℂ) * orthantSign (d l) *
          ∫ u in translatedOrientedOrthant (d l) (b l),
            orthantPolynomialTest (coordinateSpectralMeasure (ι l))
              (fun y => w l (y + ξ l)) (P l) u)) := by
    rw [← hAzero]
    refine (tendsto_const_nhds.mul (hTerm l)).congr' (Eventually.of_forall fun t => ?_)
    change ((c l : ℝ) : ℂ) * orthantSign (d l) *
      (orthantSign (d l) * ∫ y, G l t y ∂coordinateSpectralMeasure (ι l)) =
        ∫ x, J l t x ∂μ
    rw [hChange l t, mul_assoc (((c l : ℝ) : ℂ)), ← mul_assoc (orthantSign (d l)),
      Langlands.GMFamily.orthantSign_mul_self, one_mul]
  have hInW : ∀ᶠ t in 𝓝 0, ∀ x ∈ tsupport f, γ (t, x) ∈ W := by
    apply hfs.eventually_forall_of_forall_eventually
    intro x _
    exact hγ.continuous.continuousAt.eventually_mem (hW.mem_nhds (hWaxis (hγaxis x)))
  have hNear : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ l x, g l (t, x) = f x * a l (γ (t, x)) :=
    (eventually_all.mpr hge).filter_mono nhdsWithin_le_nhds
  have hEq : (fun t : ℝ => ∑ l, ∫ x, J l t x ∂μ) =ᶠ[𝓝[>] 0]
      (fun t : ℝ => ∫ x, f x * representative (γ (t, x)) ∂μ) := by
    filter_upwards [hInW.filter_mono nhdsWithin_le_nhds, hNear,
      (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))] with t ht hgt hpos
    rw [← integral_finsetSum Finset.univ (fun l _ => hInt l hpos)]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      change (∑ l, J l t x) = f x * representative (γ (t, x))
      by_cases hx : x ∈ tsupport f
      · have hNonzero (l : L) (i : ι l) : z l (γ (t, x)) i ≠ 0 := by
          intro h
          have hre := congrArg Complex.re h
          rw [hchart t x l] at hre
          exact mul_ne_zero (show 0 < t from hpos).ne' (hd l i)
            (by simpa [displacedOrthantParameter, Complex.mul_re] using hre)
        rw [hident _ (ht x hx) hNonzero, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        dsimp only [J, K]
        rw [hgt l, hchart t x l, hE]
        ring
      · simp only [J, fun l => hgs l t x hx, mul_zero, Finset.sum_const_zero,
          image_eq_zero_of_notMem_tsupport hx, zero_mul]
  exact tendsto_nhds_unique (hLimω.mono_left nhdsWithin_le_nhds)
    ((tendsto_finsetSum Finset.univ fun l _ => hLim l).congr' hEq)

theorem relativeConeFourierBoundary : RelativeConeFourierBoundaryStatement := by
  intro η L _ _ ι _ μ _ e
  obtain ⟨c, _, hc, h⟩ := relativeConeFourierBoundary_withHaar μ e
  exact ⟨c, hc, h⟩

end Langlands.Global
