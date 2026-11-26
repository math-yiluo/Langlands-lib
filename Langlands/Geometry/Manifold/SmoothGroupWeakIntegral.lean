import Langlands.Analysis.CompactManifoldIntegrableWeight
import Langlands.Automorphic.GroupSchemeAutomorphicUniformGrowthReductionProof
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Integral.Prod

/-! # Invariant differential equations for integrals tested against compact supports -/

noncomputable section

open Filter MeasureTheory Set
open scoped ContDiff Manifold Pointwise Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Geometry.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [ChartedSpace E G] [LieGroup 𝓘(ℝ, E) ∞ G]

local notation "𝓘E" => 𝓘(ℝ, E)
local notation "𝓘ℂ" => 𝓘(ℝ, ℂ)
local notation "𝔤" => GroupLieAlgebra 𝓘E G

omit [FiniteDimensional ℝ E] [LieGroup 𝓘E ∞ G] in
private theorem tsupport_groupDirectionalValue_subset (X : 𝔤) (f : G → ℂ) :
    tsupport (groupDirectionalValue 𝓘E X f) ⊆ tsupport f := by
  apply closure_minimal _ isClosed_closure
  intro g hg
  by_contra hnot
  have hn : ∀ᶠ y in 𝓝 g, y ∈ (tsupport f)ᶜ := isClosed_closure.isOpen_compl.mem_nhds hnot
  have hnear : (fun k : G => f (g * k)) =ᶠ[𝓝 1] fun _ => 0 := by
    have ht : Tendsto (fun k : G => g * k) (𝓝 1) (𝓝 g) := by
      have hc : Continuous (fun k : G => g * k) := continuous_const.mul continuous_id
      simpa only [mul_one] using hc.tendsto (1 : G)
    exact (ht.eventually hn).mono fun _ h => image_eq_zero_of_notMem_tsupport h
  apply hg
  change mvfderiv 𝓘E (fun k : G => f (g * k)) 1 X = 0
  unfold mvfderiv
  rw [hnear.mfderiv_eq, mfderiv_const]
  rfl

variable [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  (ν : Measure G) [IsFiniteMeasureOnCompacts ν] [ν.IsMulRightInvariant]

private theorem integral_directional_eq_zero {f : G → ℂ} (hf : ContMDiff 𝓘E 𝓘ℂ ∞ f)
    (hc : HasCompactSupport f) (X : 𝔤) :
    (∫ g, groupDirectionalValue 𝓘E X f g ∂ν) = 0 := by
  obtain ⟨D, hD, hD₁⟩ := exists_compact_mem_nhds (1 : G)
  let C := tsupport f * D⁻¹
  have hC : IsCompact C := hc.mul hD.inv
  have hCm : MeasurableSet C := hC.isClosed.measurableSet
  let : CompactSpace C := isCompact_iff_compactSpace.mp hC
  let νC : Measure C := ν.comap Subtype.val
  let : IsFiniteMeasureOnCompacts νC := IsFiniteMeasureOnCompacts.comap' ν continuous_subtype_val
    (MeasurableEmbedding.subtype_coe hCm)
  let j : C(C, G) := ⟨Subtype.val, continuous_subtype_val⟩
  let h (p : G × G) := f (p.2 * p.1)
  have hs : ContMDiff ((𝓘E).prod 𝓘E) 𝓘ℂ ∞ h := hf.comp (contMDiff_snd.mul contMDiff_fst)
  obtain ⟨_, _, hd⟩ := Langlands.Analysis.compactManifoldIntegrableWeight C E G E G ℂ νC
    (fun _ => 1) measurable_const (integrable_const 1) j h hs
  have hsubset (x g : G) (hg : g ∈ D) (hx : x * g ∈ tsupport f) : x ∈ C :=
    ⟨x * g, hx, g⁻¹, by simpa only [Set.mem_inv, inv_inv] using hg, mul_inv_cancel_right x g⟩
  have hconst : (fun g => ∫ x : C, f (x.val * g) ∂νC) =ᶠ[𝓝 1] fun _ => ∫ x, f x ∂ν := by
    filter_upwards [hD₁] with g hg
    rw [integral_subtype_comap hCm (fun x => f (x * g)),
      setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx => image_eq_zero_of_notMem_tsupport (fun hm => hx (hsubset x g hg hm))),
      integral_mul_right_eq_self f g]
  have hzero : mvfderiv 𝓘E (fun g => ∫ x : C, f (x.val * g) ∂νC) 1 X = 0 := by
    unfold mvfderiv
    rw [hconst.mfderiv_eq, mfderiv_const]
    rfl
  have heq := hd (1 : G) X
  change mvfderiv 𝓘E (fun g => ∫ x : C, (1 : ℂ) • f (x.val * g) ∂νC) 1 X =
    ∫ x : C, (1 : ℂ) • groupDirectionalValue 𝓘E X f x.val ∂νC at heq
  simp only [one_smul, hzero] at heq
  rw [integral_subtype_comap hCm (groupDirectionalValue 𝓘E X f)] at heq
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => ?_)).symm.trans heq.symm
  apply image_eq_zero_of_notMem_tsupport
  intro hsupp
  apply hx
  apply hsubset x 1 (mem_of_mem_nhds hD₁)
  simpa only [mul_one] using tsupport_groupDirectionalValue_subset X f hsupp

omit [FiniteDimensional ℝ E] [Group G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [MeasurableSpace G] [BorelSpace G] [LieGroup 𝓘E ∞ G] in
private theorem smooth_mul_complex {f h : G → ℂ} (hf : ContMDiff 𝓘E 𝓘ℂ ∞ f)
    (hh : ContMDiff 𝓘E 𝓘ℂ ∞ h) : ContMDiff 𝓘E 𝓘ℂ ∞ (f * h) :=
  (contDiff_mul : ContDiff ℝ ∞ (fun z : ℂ × ℂ => z.1 * z.2)).contMDiff.comp
    (hf.prodMk_space hh)

omit [FiniteDimensional ℝ E] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [MeasurableSpace G] [BorelSpace G] in
private theorem directional_product (X : 𝔤) {f h : G → ℂ}
    (hf : ContMDiff 𝓘E 𝓘ℂ ∞ f) (hh : ContMDiff 𝓘E 𝓘ℂ ∞ h) (g : G) :
    groupDirectionalValue 𝓘E X (f * h) g =
      groupDirectionalValue 𝓘E X f g * h g + f g * groupDirectionalValue 𝓘E X h g := by
  let p (z : G) := f (g * z)
  let q (z : G) := h (g * z)
  have hm : ContMDiff 𝓘E 𝓘E ∞ (fun z : G => g * z) := contMDiff_const.mul contMDiff_id
  have hp : MDifferentiableAt 𝓘E 𝓘ℂ p (1 : G) := (hf.comp hm).mdifferentiableAt (by simp)
  have hq : MDifferentiableAt 𝓘E 𝓘ℂ q (1 : G) := (hh.comp hm).mdifferentiableAt (by simp)
  have hd : mvfderiv 𝓘E (p * q) 1 = p 1 • mvfderiv 𝓘E q 1 + q 1 • mvfderiv 𝓘E p 1 :=
    (hp.hasMFDerivAt.mul hq.hasMFDerivAt).mfderiv
  change mvfderiv 𝓘E (p * q) 1 X =
    mvfderiv 𝓘E p 1 X * h g + f g * mvfderiv 𝓘E q 1 X
  rw [hd]
  simp only [add_apply, smul_apply, smul_eq_mul, show p 1 = f g by simp [p],
    show q 1 = h g by simp [q]]
  ring

private theorem integral_directional_mul {f ψ : G → ℂ}
    (hf : ContMDiff 𝓘E 𝓘ℂ ∞ f) (hψ : ContMDiff 𝓘E 𝓘ℂ ∞ ψ)
    (hc : HasCompactSupport ψ) (X : 𝔤) :
    (∫ g, groupDirectionalValue 𝓘E X f g * ψ g ∂ν) =
      ∫ g, f g * (-groupDirectionalValue 𝓘E X ψ g) ∂ν := by
  let D := groupDirectionalValue 𝓘E X
  have hDc : HasCompactSupport (D ψ) :=
    hc.of_isClosed_subset isClosed_closure (tsupport_groupDirectionalValue_subset X ψ)
  have h₁ : Integrable (fun g => D f g * ψ g) ν :=
    Continuous.integrable_of_hasCompactSupport
      ((contMDiff_groupDirectionalValue 𝓘E X hf).continuous.mul hψ.continuous) hc.mul_left
  have h₂ : Integrable (fun g => f g * D ψ g) ν :=
    Continuous.integrable_of_hasCompactSupport
      (hf.continuous.mul (contMDiff_groupDirectionalValue 𝓘E X hψ).continuous) hDc.mul_left
  have h := integral_directional_eq_zero ν (smooth_mul_complex hf hψ) hc.mul_left X
  simp_rw [directional_product X hf hψ] at h
  rw [integral_add h₁ h₂] at h
  simp only [mul_neg, integral_neg]
  exact eq_neg_of_add_eq_zero_left h

variable {n : ℕ}

omit [FiniteDimensional ℝ E] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [MeasurableSpace G] [BorelSpace G] in
private theorem smooth_word (X : Fin n → 𝔤) (w : FreeMonoid (Fin n))
    {f : G → ℂ} (hf : ContMDiff 𝓘E 𝓘ℂ ∞ f) :
    ContMDiff 𝓘E 𝓘ℂ ∞ ((lieWordDerivative X w : (G → ℂ) → G → ℂ) f) := by
  induction w using FreeMonoid.inductionOn' with
  | one => simpa only [lieWordDerivative_one] using hf
  | of_mul i w ih =>
    rw [lieWordDerivative_of_mul]
    exact contMDiff_groupDirectionalValue 𝓘E _ ih

private theorem exists_word_adjoint (X : Fin n → 𝔤) (w : FreeMonoid (Fin n))
    {ψ : G → ℂ} (hψ : ContMDiff 𝓘E 𝓘ℂ ∞ ψ) (hc : HasCompactSupport ψ) :
    ∃ χ : G → ℂ, ContMDiff 𝓘E 𝓘ℂ ∞ χ ∧ tsupport χ ⊆ tsupport ψ ∧
      ∀ f : G → ℂ, ContMDiff 𝓘E 𝓘ℂ ∞ f →
        (∫ g, (lieWordDerivative X w : (G → ℂ) → G → ℂ) f g * ψ g ∂ν) =
          ∫ g, f g * χ g ∂ν := by
  induction w using FreeMonoid.inductionOn' generalizing ψ with
  | one => exact ⟨ψ, hψ, subset_rfl, fun f _ => by simp only [lieWordDerivative_one]⟩
  | of_mul i w ih =>
    let χ₀ : G → ℂ := -groupDirectionalValue 𝓘E (X i) ψ
    have hc₀ : tsupport χ₀ ⊆ tsupport ψ := by
      simpa only [χ₀, tsupport_neg] using tsupport_groupDirectionalValue_subset (X i) ψ
    obtain ⟨χ, hχ, hsub, hAdj⟩ := ih
      (contMDiff_groupDirectionalValue 𝓘E (X i) hψ).neg
      (hc.of_isClosed_subset isClosed_closure hc₀)
    refine ⟨χ, hχ, hsub.trans hc₀, fun f hf => ?_⟩
    simp only [lieWordDerivative_of_mul]
    exact (integral_directional_mul ν (smooth_word X w hf) hψ hc (X i)).trans (hAdj f hf)

omit [FiniteDimensional ℝ E] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [MeasurableSpace G] [BorelSpace G] in
private theorem smooth_wordAction (X : Fin n → 𝔤) (P : MonoidAlgebra ℂ (FreeMonoid (Fin n)))
    {f : G → ℂ} (hf : ContMDiff 𝓘E 𝓘ℂ ∞ f) : ContMDiff 𝓘E 𝓘ℂ ∞ (lieWordAction X P f) := by
  induction P using MonoidAlgebra.induction_linear with
  | zero => rw [lieWordAction_zero]; exact contMDiff_const
  | add P Q hP hQ => rw [lieWordAction_add]; exact hP.add hQ
  | single w c =>
    rw [lieWordAction_single]
    exact smooth_mul_complex contMDiff_const (smooth_word X w hf)

private theorem exists_wordAction_adjoint (X : Fin n → 𝔤)
    (P : MonoidAlgebra ℂ (FreeMonoid (Fin n)))
    {ψ : G → ℂ} (hψ : ContMDiff 𝓘E 𝓘ℂ ∞ ψ) (hc : HasCompactSupport ψ) :
    ∃ χ : G → ℂ, ContMDiff 𝓘E 𝓘ℂ ∞ χ ∧ tsupport χ ⊆ tsupport ψ ∧
      ∀ f : G → ℂ, ContMDiff 𝓘E 𝓘ℂ ∞ f →
        (∫ g, lieWordAction X P f g * ψ g ∂ν) = ∫ g, f g * χ g ∂ν := by
  induction P using MonoidAlgebra.induction_linear with
  | zero =>
    exact ⟨0, contMDiff_const, by simp, fun f _ => by simp [lieWordAction_zero]⟩
  | add P Q hP hQ =>
    obtain ⟨χ, hχ, hcχ, haχ⟩ := hP
    obtain ⟨η, hη, hcη, haη⟩ := hQ
    have hSub : tsupport (χ + η) ⊆ tsupport ψ := by
      apply closure_minimal _ isClosed_closure
      intro g hg
      by_contra hnot
      exact hg (by simp only [Pi.add_apply,
        image_eq_zero_of_notMem_tsupport (fun h => hnot (hcχ h)),
        image_eq_zero_of_notMem_tsupport (fun h => hnot (hcη h)), add_zero])
    refine ⟨χ + η, hχ.add hη, hSub, fun f hf => ?_⟩
    have hi (R : MonoidAlgebra ℂ (FreeMonoid (Fin n))) :
        Integrable (fun g => lieWordAction X R f g * ψ g) ν :=
      ((smooth_wordAction X R hf).continuous.mul hψ.continuous).integrable_of_hasCompactSupport
        hc.mul_left
    have hiχ : Integrable (fun g => f g * χ g) ν :=
      (hf.continuous.mul hχ.continuous).integrable_of_hasCompactSupport
        (show HasCompactSupport χ from hc.of_isClosed_subset isClosed_closure hcχ).mul_left
    have hiη : Integrable (fun g => f g * η g) ν :=
      (hf.continuous.mul hη.continuous).integrable_of_hasCompactSupport
        (show HasCompactSupport η from hc.of_isClosed_subset isClosed_closure hcη).mul_left
    simp only [lieWordAction_add, Pi.add_apply, add_mul, mul_add]
    rw [integral_add (hi P) (hi Q), integral_add hiχ hiη, haχ f hf, haη f hf]
  | single w c =>
    obtain ⟨χ, hχ, hcχ, haχ⟩ := exists_word_adjoint ν X w hψ hc
    refine ⟨fun g => c * χ g, smooth_mul_complex contMDiff_const hχ, ?_, fun f hf => ?_⟩
    · exact tsupport_mul_subset_right.trans hcχ
    · simp only [lieWordAction_single, Pi.smul_apply, smul_eq_mul, mul_assoc]
      rw [integral_const_mul, haχ f hf]
      simp_rw [mul_left_comm (f _) c]
      rw [integral_const_mul]

variable [SigmaCompactSpace G] [ν.IsOpenPosMeasure]

omit [IsTopologicalGroup G] [ν.IsMulRightInvariant] in
private theorem eq_zero_of_integral_tests {u : G → ℂ} (hu : Continuous u)
    (hz : ∀ ψ : G → ℂ, ContMDiff 𝓘E 𝓘ℂ ∞ ψ → HasCompactSupport ψ →
      (∫ g, u g * ψ g ∂ν) = 0) : u = 0 := by
  funext x
  by_contra hnot
  change u x ≠ 0 at hnot
  let c : ℂ := (starRingEnd ℂ) (u x)
  let realValue (g : G) := (u g * c).re
  have hr : Continuous realValue := Complex.continuous_re.comp (hu.mul continuous_const)
  have hrx : 0 < realValue x := by
    change 0 < (u x * (starRingEnd ℂ) (u x)).re
    rw [Complex.mul_conj, Complex.ofReal_re]
    exact Complex.normSq_pos.mpr hnot
  obtain ⟨D, hD, hxD⟩ := exists_compact_mem_nhds x
  let S := interior D ∩ {g : G | 0 < realValue g}
  have hS : IsOpen S := isOpen_interior.inter (isOpen_lt continuous_const hr)
  have hxS : x ∈ S := ⟨mem_interior_iff_mem_nhds.mpr hxD, hrx⟩
  obtain ⟨b, hb, hbs, hb₀⟩ := hS.exists_contMDiff_support_eq (n := (⊤ : ℕ∞)) 𝓘E
  let ψ (g : G) : ℂ := c * (b g : ℂ)
  have hbsupp : HasCompactSupport b :=
    hD.of_isClosed_subset isClosed_closure (closure_minimal (hb ▸ inter_subset_left.trans
      interior_subset) hD.isClosed)
  have hψc : HasCompactSupport ψ :=
    hbsupp.comp_left (g := fun r : ℝ => c * (r : ℂ)) (by simp)
  have hψs : ContMDiff 𝓘E 𝓘ℂ ∞ ψ :=
    smooth_mul_complex contMDiff_const (Complex.ofRealCLM.contDiff.contMDiff.comp hbs)
  have hbx : x ∈ Function.support b := hb.symm ▸ hxS
  have hbPos : 0 < b x := lt_of_le_of_ne (hb₀ x) (Ne.symm hbx)
  have hreal (g : G) : (u g * ψ g).re = realValue g * b g := by
    change (u g * (c * (b g : ℂ))).re = _
    rw [← mul_assoc]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, realValue]
  have hnonneg (g : G) : 0 ≤ realValue g * b g := by
    by_cases hg : g ∈ Function.support b
    · rw [hb] at hg
      exact mul_nonneg hg.2.le (hb₀ g)
    · rw [Function.notMem_support.mp hg, mul_zero]
  have hpos : 0 < ∫ g, realValue g * b g ∂ν :=
    (hr.mul hbs.continuous).integral_pos_of_hasCompactSupport_nonneg_nonzero hbsupp.mul_left
      hnonneg (mul_pos hrx hbPos).ne'
  have hi : Integrable (fun g => u g * ψ g) ν :=
    (hu.mul hψs.continuous).integrable_of_hasCompactSupport hψc.mul_left
  have hRe := Complex.reCLM.integral_comp_comm hi
  change (∫ g, (u g * ψ g).re ∂ν) = (∫ g, u g * ψ g ∂ν).re at hRe
  simp_rw [hreal] at hRe
  rw [hz ψ hψs hψc, Complex.zero_re] at hRe
  exact hpos.ne' hRe

/-- A homogeneous invariant differential equation is preserved by a smooth integral on a
finite-dimensional real Lie group. The group is Hausdorff, locally compact and sigma-compact
with its Borel measurable structure. The group measure is right invariant, finite on compacts
and positive on nonempty opens. Both measures are s-finite. Integrability of the values
against compact continuous tests supplies the Fubini step. -/
def SmoothGroupWeakIntegralStatement
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [ChartedSpace E G] [LieGroup 𝓘(ℝ, E) ∞ G]
    [T2Space G] [LocallyCompactSpace G] [SigmaCompactSpace G]
    [MeasurableSpace G] [BorelSpace G] {n : ℕ} : Prop :=
  ∀ (ν : Measure G) [IsFiniteMeasureOnCompacts ν] [ν.IsOpenPosMeasure] [ν.IsMulRightInvariant]
    [SFinite ν] (T : Type*) [MeasurableSpace T] (μ : Measure T) [SFinite μ]
    (X : Fin n → GroupLieAlgebra 𝓘(ℝ, E) G) (P : MonoidAlgebra ℂ (FreeMonoid (Fin n)))
    (f : T → G → ℂ),
      (∀ t, ContMDiff 𝓘(ℝ, E) 𝓘ℂ ∞ (f t)) →
      (∀ t, lieWordAction X P (f t) = 0) →
      (∀ ψ : G → ℂ, Continuous ψ → HasCompactSupport ψ →
        Integrable (fun p : G × T => f p.2 p.1 * ψ p.1) (ν.prod μ)) →
      let u (g : G) := ∫ t, f t g ∂μ
      ContMDiff 𝓘(ℝ, E) 𝓘ℂ ∞ u → lieWordAction X P u = 0

theorem smoothGroupWeakIntegral :
    SmoothGroupWeakIntegralStatement (E := E) (G := G) (n := n) := by
  intro ν _ _ _ _ T _ μ _ X P f hf hP hint u hu
  apply eq_zero_of_integral_tests (E := E) ν (smooth_wordAction X P hu).continuous
  intro ψ hψ hc
  obtain ⟨χ, hχ, hsub, hAdj⟩ := exists_wordAction_adjoint ν X P hψ hc
  have hχc : HasCompactSupport χ := hc.of_isClosed_subset isClosed_closure hsub
  rw [hAdj u hu]
  have hi := hint χ hχ.continuous hχc
  change (∫ g, (∫ t, f t g ∂μ) * χ g ∂ν) = 0
  simp_rw [← integral_mul_const]
  rw [integral_integral_swap hi]
  have hpair (t : T) : (∫ g, f t g * χ g ∂ν) = 0 := by
    rw [← hAdj (f t) (hf t), hP t]
    simp
  simp_rw [hpair, integral_zero]

end Langlands.Geometry.Manifold
