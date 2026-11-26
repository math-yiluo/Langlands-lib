import Langlands.Global.AdelicEisensteinFiniteSlices
import Langlands.Global.AdelicEisensteinDifferentialParameters
import Langlands.Global.AdelicEisensteinCompactBounds
import Langlands.Global.AdelicMaximalCompactFactors
import Langlands.Global.AdelicGroupPolish
import Langlands.Analysis.CompactManifoldIntegrableWeight
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Group.Integral

/-! # Smooth archimedean Iwasawa height for a supplied maximal compact -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry Filter MeasureTheory NumberField IsDedekindDomain
  Set Topology TopologicalSpace
open scoped ContDiff Manifold Pointwise

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Langlands.Global

section Smoothing

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type w} [Group H] [TopologicalSpace H] [ChartedSpace E H] [LieGroup 𝓘(ℝ, E) ∞ H]
  [IsTopologicalGroup H] [T2Space H] [LocallyCompactSpace H]

local notation "IH" => 𝓘(ℝ, E)
local notation "IC" => 𝓘(ℝ, ℂ)

private theorem contMDiff_rightAverage [MeasurableSpace H] [BorelSpace H]
    (μ : Measure H) [μ.IsHaarMeasure] {f h : H → ℂ}
    (hf : Continuous f) (hh : ContMDiff IH IC ∞ h) (hc : HasCompactSupport h) :
    ContMDiff IH IC ∞ (fun x => ∫ y, h y * f (x * y) ∂μ) := by
  intro x
  obtain ⟨V, hVc, hV⟩ := exists_compact_mem_nhds x
  let C := V * tsupport h
  have hC : IsCompact C := hVc.mul hc
  let : CompactSpace C := isCompact_iff_compactSpace.mp hC
  let ν : Measure C := μ.comap Subtype.val
  have hfi : Integrable (fun y : C => f y.val) ν :=
    (integrableOn_iff_comap_subtypeVal hC.isClosed.measurableSet).mp
      (hf.continuousOn.integrableOn_compact hC)
  let j : C(C, H) := ⟨Subtype.val, continuous_subtype_val⟩
  let k (p : H × H) := h (p.1⁻¹ * p.2)
  have hk : ContMDiff ((IH).prod IH) IC ∞ k := hh.comp (contMDiff_fst.inv.mul contMDiff_snd)
  obtain ⟨_, hs, _⟩ := Langlands.Analysis.compactManifoldIntegrableWeight C E H E H ℂ
    ν (fun y => f y.val) (hf.measurable.comp measurable_subtype_coe) hfi j k hk
  apply (hs x).congr_of_eventuallyEq
  filter_upwards [hV] with z hz
  symm
  change (∫ y : C, f y.val * h (z⁻¹ * y.val) ∂ν) = ∫ y, h y * f (z * y) ∂μ
  rw [integral_subtype_comap hC.isClosed.measurableSet (fun y => f y * h (z⁻¹ * y))]
  have heq : (∫ y in C, f y * h (z⁻¹ * y) ∂μ) = ∫ y, f y * h (z⁻¹ * y) ∂μ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    have hzero : z⁻¹ * y ∉ tsupport h := by
      intro hmem
      exact hy ⟨z, hz, z⁻¹ * y, hmem, mul_inv_cancel_left _ _⟩
    rw [image_eq_zero_of_notMem_tsupport hzero, mul_zero]
  rw [heq, ← integral_mul_left_eq_self (μ := μ) (fun y => f y * h (z⁻¹ * y)) z]
  simp only [inv_mul_cancel_left, mul_comm]

private theorem exists_compact_smooth_leftInvariantKernel [SigmaCompactSpace H] [NormalSpace H]
    (K : Subgroup H) (hK : IsCompact (K : Set H)) :
    ∃ h : H → ℝ, ContMDiff IH 𝓘(ℝ) ∞ h ∧ HasCompactSupport h ∧
      (∀ x, 0 ≤ h x) ∧ h 1 = 1 ∧ ∀ k ∈ K, ∀ x, h (k * x) = h x := by
  obtain ⟨V, hV, hKV⟩ := exists_compact_superset hK
  obtain ⟨b, hbone, hbzero, hb01⟩ := exists_contMDiffMap_one_nhds_of_subset_interior IH
    (n := (⊤ : ℕ∞)) hK.isClosed hKV
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : MeasurableSpace K := borel K
  let : BorelSpace K := ⟨rfl⟩
  let μ : Measure K := Measure.haarMeasure (⊤ : PositiveCompacts K)
  let : μ.IsHaarMeasure := by dsimp [μ]; infer_instance
  have hμ : μ Set.univ = 1 := by
    simpa only [μ, PositiveCompacts.coe_top] using
      (Measure.haarMeasure_self (K₀ := (⊤ : PositiveCompacts K)))
  let j : C(K, H) := ⟨Subtype.val, continuous_subtype_val⟩
  let k (p : H × H) : ℂ := b (p.2⁻¹ * p.1)
  have hk : ContMDiff ((IH).prod IH) IC ∞ k :=
    (Complex.ofRealCLM.contDiff (n := ∞)).contMDiff.comp
      (b.contMDiff.comp (contMDiff_snd.inv.mul contMDiff_fst))
  obtain ⟨_, havg, _, _⟩ := Langlands.Analysis.compactManifoldVectorIntegral K E H E H ℂ
    μ (1 : C(K, ℂ)) j k hk
  let h (x : H) : ℝ := ∫ y : K, b (y.val⁻¹ * x) ∂μ
  have hdiff : ContMDiff IH 𝓘(ℝ) ∞ h := by
    apply ((Complex.reCLM.contDiff (n := ∞)).contMDiff.comp havg).congr
    intro x
    change h x = (∫ y : K, (1 : ℂ) • ((b (y.val⁻¹ * x) : ℝ) : ℂ) ∂μ).re
    rw [show (fun y : K => (1 : ℂ) • ((b (y.val⁻¹ * x) : ℝ) : ℂ)) =
      (fun y : K => ((b (y.val⁻¹ * x) : ℝ) : ℂ)) from funext fun _ => one_smul _ _]
    rw [integral_complex_ofReal, Complex.ofReal_re]
  refine ⟨h, hdiff, ?_, fun x => integral_nonneg (fun y => (hb01 _).1), ?_, ?_⟩
  · show IsCompact (tsupport h)
    apply (hK.mul hV).of_isClosed_subset (isClosed_tsupport h)
    apply closure_minimal _ (hK.mul hV).isClosed
    intro x hx
    by_contra hnot
    apply hx
    have hzero (y : K) : b (y.val⁻¹ * x) = 0 := hbzero _ (fun hy =>
      hnot ⟨y.val, y.property, y.val⁻¹ * x, hy, mul_inv_cancel_left _ _⟩)
    simp only [h, hzero, integral_zero]
  · have hconst (y : K) : b (y.val⁻¹) = 1 :=
      hbone.self_of_nhdsSet _ (show y.val⁻¹ ∈ (K : Set H) from K.inv_mem y.property)
    simp only [h, hconst, integral_const, measureReal_def, hμ, ENNReal.toReal_one, smul_eq_mul,
      mul_one]
  · intro a ha x
    let aK : K := ⟨a, ha⟩
    dsimp only [h]
    rw [← integral_mul_left_eq_self (μ := μ) (fun y : K => b (y.val⁻¹ * (a * x))) aK]
    simp only [Subgroup.coe_mul, mul_inv_rev, aK, mul_assoc, inv_mul_cancel_left]

/-- A continuous right-compact-invariant function whose left parabolic increments
are constant is smooth when the parabolic and compact factors cover the group. -/
private theorem contMDiff_of_additiveIwasawa [SigmaCompactSpace H] [NormalSpace H]
    (P K : Subgroup H) (hK : IsCompact (K : Set H))
    (hcover : ∀ x : H, ∃ p ∈ P, ∃ k ∈ K, p * k = x) {f : H → ℂ}
    (hf : Continuous f) (hleft : ∀ p ∈ P, ∀ x, f (p * x) = f p + f x)
    (hright : ∀ k ∈ K, ∀ x, f (x * k) = f x) : ContMDiff IH IC ∞ f := by
  let : MeasurableSpace H := borel H
  let : BorelSpace H := ⟨rfl⟩
  let μ : Measure H := Measure.haar
  let : μ.IsHaarMeasure := by dsimp [μ]; infer_instance
  obtain ⟨b, hb, hbc, hb0, hb1, hbi⟩ :=
    exists_compact_smooth_leftInvariantKernel (E := E) K hK
  let h (x : H) : ℂ := b x
  have hh : ContMDiff IH IC ∞ h := (Complex.ofRealCLM.contDiff (n := ∞)).contMDiff.comp hb
  have hc : HasCompactSupport h := by
    apply hbc.of_isClosed_subset (isClosed_tsupport h)
    apply closure_mono
    intro y hy hby
    exact hy (by simp [h, hby])
  let mass : ℂ := ∫ y, h y ∂μ
  have hmass : mass ≠ 0 := by
    change (∫ y, ((b y : ℝ) : ℂ) ∂μ) ≠ 0
    rw [integral_complex_ofReal]
    exact Complex.ofReal_ne_zero.mpr
      (integral_pos_of_integrable_nonneg_nonzero hb.continuous
        (hb.continuous.integrable_of_hasCompactSupport hbc) hb0 (hb1.trans_ne one_ne_zero)).ne'
  let A (x : H) := ∫ y, h y * f (x * y) ∂μ
  have hA : ContMDiff IH IC ∞ A := contMDiff_rightAverage μ hf hh hc
  let c := ∫ y, h y * f y ∂μ
  have heq (x : H) : A x = f x * mass + c := by
    obtain ⟨p, hp, k, hk, rfl⟩ := hcover x
    dsimp only [A]
    rw [← integral_mul_left_eq_self (μ := μ) (fun y => h y * f ((p * k) * y)) k⁻¹]
    have hpoint (y : H) : h (k⁻¹ * y) * f ((p * k) * (k⁻¹ * y)) =
        f p * h y + h y * f y := by
      rw [mul_assoc p k, mul_inv_cancel_left, hleft p hp, show h (k⁻¹ * y) = h y by
        exact congrArg Complex.ofReal (hbi k⁻¹ (K.inv_mem hk) y)]
      ring
    simp_rw [hpoint]
    have h1 : Integrable (fun y => f p * h y) μ :=
      (continuous_const.mul hh.continuous).integrable_of_hasCompactSupport
        (hc.of_isClosed_subset (isClosed_tsupport _) (closure_mono
          (Function.support_mul_subset_right (fun _ => f p) h)))
    have h2 : Integrable (fun y => h y * f y) μ :=
      (hh.continuous.mul hf).integrable_of_hasCompactSupport
        (hc.of_isClosed_subset (isClosed_tsupport _) (closure_mono
          (Function.support_mul_subset_left h f)))
    rw [integral_add h1 h2, integral_const_mul, hright k hk]
  apply (((ContinuousLinearMap.mul ℝ ℂ mass⁻¹).contDiff (n := ∞)).contMDiff.comp
    (hA.sub (contMDiff_const (c := c)))).congr
  intro x
  change f x = mass⁻¹ * (A x - c)
  rw [heq, add_sub_cancel_right, mul_comm (f x), ← mul_assoc, inv_mul_cancel₀ hmass, one_mul]

end Smoothing

open scoped CategoryTheory.MonObj

namespace AdelicGroupPoints.IsIwasawaCompact

open InfiniteAdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine P.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {K : Subgroup (AdelicGroupPoints F G)}
  (hK : IsIwasawaCompact p K) (hmax : IsMaximalCompactSubgroup F G K)

include hmax in
/-- The Iwasawa height of a pair is the sum of its infinite and finite heights. -/
theorem height_pair_of_maximal (a : InfiniteAdelicGroupPoints F G)
    (b : FiniteAdelicGroupPoints F G) :
    hK.height (pair F G a b) = hK.height (ofInfinite F G a) + hK.height (ofFinite F G b) := by
  have h := hK.finiteHeightDisplacement_pair
    (fun k hk => ((hmax.mem_iff k).mp hk).1) b 1 a
  have h0 : hK.height (pair F G 1 1) = 0 := by
    rw [← ofFinite_eq_pair, map_one, hK.height_of_mem K.one_mem]
  simp only [finiteHeightDisplacement, ofFinite_eq_pair, pair_mul, mul_one, one_mul, h0,
    sub_zero] at h
  exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)

variable [LocallyOfFiniteType G.X.hom] {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)

include hmax in
/-- For any maximal Iwasawa compact, the actual complex height pairings are smooth
on every infinite slice. -/
theorem hasSmoothHeightPairings_of_maximal : hK.HasSmoothHeightPairings hsmooth := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let H := InfiniteAdelicGroupPoints F G
  let Kinf := K.comap (ofInfinite F G).toMonoidHom
  let m := P.affinePointsTarget p (CommAlgCat.of F (InfiniteAdeleRing F))
  let Pinf := m.range
  have hcover (x : H) : ∃ y ∈ Pinf, ∃ k ∈ Kinf, y * k = x := by
    obtain ⟨q, k, hk, heq⟩ := hK.exists_eq (ofInfinite F G x)
    refine ⟨m (infinite F P q), ⟨_, rfl⟩, infinite F G k, ((hmax.mem_iff k).mp hk).1, ?_⟩
    have hn : infinite F G (map F P G p q) =
        P.affinePointsTarget p (CommAlgCat.of F (InfiniteAdeleRing F)) (infinite F P q) :=
      DFunLike.congr_fun (P.affinePointsTarget_naturality p
        (CommAlgCat.ofHom (AlgHom.fst F (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)))) q
    simpa only [map_mul, hn, infinite_ofInfinite] using congrArg (infinite F G) heq
  intro lam b
  let f (x : H) := complexParameterPairing F P lam (hK.height (ofInfinite F G x))
  have hf : Continuous f := (continuous_complexParameterPairing_apply lam).comp
    (hK.continuous_height.comp (ofInfinite F G).continuous)
  have hleft (y : H) (hy : y ∈ Pinf) (x : H) : f (y * x) = f y + f x := by
    obtain ⟨q, rfl⟩ := hy
    have hq : map F P G p (ofInfinite F P q) = ofInfinite F G (m q) :=
      map_ofInfinite p q
    simp only [f, map_mul, ← hq, hK.height_map_mul, hK.height_map, map_add]
  have hright (k : H) (hk : k ∈ Kinf) (x : H) : f (x * k) = f x := by
    change ofInfinite F G k ∈ K at hk
    simp only [f, map_mul, hK.height_mul_right _ hk]
  have hsm : ContMDiff 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, ℂ) ∞ f :=
    contMDiff_of_additiveIwasawa Pinf Kinf
      hmax.isMaximalCompact_comap_ofInfinite.1 hcover hf hleft hright
  apply (hsm.add (contMDiff_const (c := complexParameterPairing F P lam (hK.height (ofFinite F G b))))).congr
  intro x
  simp only [f, hK.height_pair_of_maximal hmax, map_add, Pi.add_apply]

end AdelicGroupPoints.IsIwasawaCompact

end Langlands.Global
