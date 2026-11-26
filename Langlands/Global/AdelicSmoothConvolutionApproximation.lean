import Langlands.Automorphic.GroupSchemeManifoldSmooth
import Langlands.Global.AdelicLocalFinitenessStatement
import Langlands.Global.FiniteAdelicGroupCompactOpenBasisProof
import Mathlib.Geometry.Manifold.BumpFunction

/-! # Approximation by smooth adelic convolution kernels -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Filter MeasureTheory NumberField Set
open scoped CategoryTheory.MonObj ContDiff Manifold Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.AdelicGroupPoints

open InfiniteAdelicGroupPoints Langlands.Automorphic.GroupSchemeFunctions

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

local notation "A" => AdelicGroupPoints F G
local notation "A∞" => InfiniteAdelicGroupPoints F G
local notation "A_f" => FiniteAdelicGroupPoints F G
local notation "dg" => (Measure.haar : Measure A)

/-- A nonnegative smooth test kernel of integral one can be supported in
any identity neighborhood in the actual adelic group. -/
theorem exists_normalizedAdelicTestFunction {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    {V : Set A} (hV : V ∈ 𝓝 1) :
    ∃ h : A → ℝ, IsAdelicTestFunction F G (fun x => (h x : ℂ)) ∧
      tsupport h ⊆ V ∧ (∀ x, 0 ≤ h x) ∧ (∫ x, h x ∂dg) = 1 := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothIsManifold F G hsmooth
  have hsplit : (split F G).symm ⁻¹' V ∈ 𝓝 (1 : A∞ × A_f) := by
    apply (split F G).symm.continuous.continuousAt.preimage_mem_nhds
    change V ∈ 𝓝 ((split F G).symm (1 : A∞ × A_f))
    rwa [map_one]
  rw [show (1 : A∞ × A_f) = ((1 : A∞), (1 : A_f)) from rfl, nhds_prod_eq, Filter.mem_prod_iff]
    at hsplit
  obtain ⟨Vi, hVi, Vf, hVf, hbox⟩ := hsplit
  obtain ⟨b, -, hbV⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, smoothModel F d)) (1 : A∞)).mem_iff.mp hVi
  obtain ⟨L, hLc, hLV⟩ := ((finiteAdelicGroupCompactOpenBasis F G).2.mem_iff).mp hVf
  let ind : A_f → ℝ := (L : Set A_f).indicator (fun _ => 1)
  let kernel (x : A) : ℝ := b (infinite F G x) * ind (finite F G x)
  have hind : Continuous ind := L.isClopen.continuous_indicator continuous_const
  have hkernel : Continuous kernel :=
    (b.continuous.comp (infinite F G).continuous).mul (hind.comp (finite F G).continuous)
  let box : Set A := (split F G) ⁻¹' (tsupport (b : A∞ → ℝ) ×ˢ (L : Set A_f))
  have hboxc : IsCompact box :=
    (split F G).toHomeomorph.isCompact_preimage.mpr (b.hasCompactSupport.prod hLc)
  have hsupport : tsupport kernel ⊆ box := by
    refine closure_minimal ?_ hboxc.isClosed
    intro x hx
    have hx' : b (infinite F G x) * ind (finite F G x) ≠ 0 := hx
    obtain ⟨hi, hf⟩ := mul_ne_zero_iff.mp hx'
    exact ⟨subset_tsupport _ hi, by simpa [ind, Set.indicator] using hf⟩
  have hboxV : box ⊆ V := by
    intro x hx
    have hmem := hbox (a := split F G x) ⟨hbV hx.1, hLV hx.2⟩
    change (split F G).symm ((split F G) x) ∈ V at hmem
    rwa [(split F G).symm_apply_apply] at hmem
  have hnonneg (x : A) : 0 ≤ kernel x :=
    mul_nonneg b.nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
  have hpos : 0 < ∫ x, kernel x ∂dg :=
    hkernel.integral_pos_of_hasCompactSupport_nonneg_nonzero (hboxc.of_isClosed_subset
      isClosed_closure hsupport) hnonneg (x := 1) (by
        simp [kernel, ind, map_one])
  let c : ℝ := (∫ x, kernel x ∂dg)⁻¹
  let h (x : A) := c * kernel x
  have hc : 0 ≤ c := inv_nonneg.mpr hpos.le
  have hhcont : Continuous h := continuous_const.mul hkernel
  have hhsupp : tsupport h ⊆ box := tsupport_mul_subset_right.trans hsupport
  refine ⟨h, ?_, hhsupp.trans hboxV, fun x => mul_nonneg hc (hnonneg x), ?_⟩
  · have hEq {y z : A_f} (hyz : y ∈ L ↔ z ∈ L) : ind y = ind z := by
      by_cases hy : y ∈ L
      · simp [ind, hy, hyz.mp hy]
      · have hz : z ∉ (L : Set A_f) := fun hz => hy (hyz.mpr hz)
        simp [ind, hy, hz]
    have hcompact : HasCompactSupport h :=
      hboxc.of_isClosed_subset isClosed_closure hhsupp
    refine ⟨⟨Complex.continuous_ofReal.comp hhcont, ?_, L.toSubgroup, L.isOpen, ?_⟩,
      hcompact.comp_left Complex.ofReal_zero,
      L.toSubgroup, L.isOpen, ?_⟩
    · intro x
      apply (isPlotSmooth_iff_contMDiff F G hsmooth _).2
      let mulConst := (ContinuousLinearMap.id ℝ ℝ).smulRight (c * ind x)
      apply (Complex.ofRealCLM.contMDiff.comp (mulConst.contMDiff.comp b.contMDiff)).congr
      intro a
      change ((c * (b (infinite F G (pair F G a x)) * ind (finite F G (pair F G a x))) : ℝ) : ℂ) =
        ((b a * (c * ind x) : ℝ) : ℂ)
      rw [infinite_pair, finite_pair]
      exact congrArg Complex.ofReal (by ring)
    · intro l hl x
      have hEq' := hEq (show finite F G x * l ∈ L ↔ finite F G x ∈ L from L.mul_mem_cancel_right hl)
      simp only [h, kernel, map_mul, infinite_ofFinite, mul_one, finite_ofFinite, hEq']
    · intro l hl x
      have hEq' := hEq (show l * finite F G x ∈ L ↔ finite F G x ∈ L from L.mul_mem_cancel_left hl)
      simp only [h, kernel, map_mul, infinite_ofFinite, one_mul, finite_ofFinite, hEq']
  · change (∫ x, c * kernel x ∂dg) = 1
    rw [integral_const_mul]
    exact inv_mul_cancel₀ hpos.ne'

/-- Normalized smooth adelic test kernels approximate a finite family of continuous functions
uniformly on a compact set under right convolution. -/
theorem exists_rightConvolution_approximation {d m : ℕ}
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) (f : Fin m → C(A, ℂ))
    {C : Set A} (hC : IsCompact C) {ε : ℝ} (hε : 0 < ε) :
    ∃ h : A → ℂ, IsAdelicTestFunction F G h ∧
      ∀ i x, x ∈ C → ‖rightConvolution F G h (f i) x - f i x‖ ≤ ε := by
  let H (i : Fin m) (g x : A) := ‖f i (x * g) - f i x‖
  let V : Set A := {g | ∀ i, ∀ x ∈ C, H i g x < ε}
  have hV : V ∈ 𝓝 (1 : A) := by
    change ∀ᶠ g in 𝓝 (1 : A), ∀ i, ∀ x ∈ C, H i g x < ε
    rw [Filter.eventually_all]
    intro i
    apply hC.eventually_forall_of_forall_eventually
    intro x _
    have hcont : Continuous (Function.uncurry (H i)) :=
      (((f i).continuous.comp (continuous_snd.mul continuous_fst)).sub
        ((f i).continuous.comp continuous_snd)).norm
    exact hcont.continuousAt.eventually_lt (g := fun _ => ε) continuousAt_const
      (by simpa [H] using hε)
  obtain ⟨h, hh, hsupport, hnonneg, hmass⟩ := exists_normalizedAdelicTestFunction hsmooth hV
  refine ⟨fun g => (h g : ℂ), hh, ?_⟩
  intro i x hx
  have hInt : Integrable (fun g => (h g : ℂ) * f i (x * g)) dg :=
    (hh.1.1.mul ((f i).continuous.comp (continuous_const.mul continuous_id)))
      |>.integrable_of_hasCompactSupport hh.2.1.mul_right
  have hconst : Integrable (fun g => (h g : ℂ) * f i x) dg :=
    (hh.1.1.mul continuous_const).integrable_of_hasCompactSupport hh.2.1.mul_right
  have hEq : (∫ g, (h g : ℂ) * f i x ∂dg) = f i x := by
    rw [integral_mul_const, integral_complex_ofReal, hmass, Complex.ofReal_one, one_mul]
  calc
    _ = ‖∫ g, (h g : ℂ) * (f i (x * g) - f i x) ∂dg‖ := by
      simp only [mul_sub, integral_sub hInt hconst, hEq, rightConvolution]
    _ ≤ ∫ g, ε * h g ∂dg := norm_integral_le_of_norm_le ?_ ?_
    _ = ε := by rw [integral_const_mul, hmass, mul_one]
  · exact (Complex.continuous_re.comp hh.1.1).integrable_of_hasCompactSupport
      (hh.2.1.comp_left Complex.zero_re) |>.const_mul ε
  · apply Filter.Eventually.of_forall
    intro g
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hnonneg g), mul_comm ε]
    by_cases hg : g ∈ tsupport h
    · exact mul_le_mul_of_nonneg_left ((hsupport hg) i x hx).le (hnonneg g)
    · rw [image_eq_zero_of_notMem_tsupport hg, zero_mul, zero_mul]

end Langlands.Global.AdelicGroupPoints

namespace Langlands.Global

open AdelicGroupPoints

/-- Smooth right convolution approximates a finite family of continuous adelic functions
uniformly on any specified compact set. -/
def AdelicConvolutionApproximationStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    {d : ℕ}, SmoothOfRelativeDimension d G.X.hom →
    ∀ {m : ℕ} (f : Fin m → C(AdelicGroupPoints F G, ℂ))
      (S : Set (AdelicGroupPoints F G)), IsCompact S → ∀ ε : ℝ, 0 < ε →
      ∃ h : AdelicGroupPoints F G → ℂ, IsAdelicTestFunction F G h ∧
        ∀ i x, x ∈ S → ‖rightConvolution F G h (f i) x - f i x‖ ≤ ε

theorem adelicConvolutionApproximation : AdelicConvolutionApproximationStatement.{u} := by
  intro F _ _ G _ _ d hsmooth m f S hS ε hε
  exact exists_rightConvolution_approximation hsmooth f hS hε

end Langlands.Global
