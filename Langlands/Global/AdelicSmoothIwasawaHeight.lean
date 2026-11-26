import Langlands.Global.AdelicEisensteinDifferentialParameters
import Langlands.Global.AdelicRightConvolutionDifferentiation
import Langlands.Global.AdelicEisensteinFiniteCompactChangeProof
import Langlands.Global.AdelicMaximalCompactFactors
import Langlands.Global.EisensteinConstantTerm.Height
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-! # Smooth adelic Iwasawa height pairings by convolution -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory NumberField Topology Filter
open scoped CategoryTheory.MonObj Manifold ContDiff Pointwise

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions InfiniteAdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)

local notation "H" => AdelicGroupPoints F G
local notation "H∞" => InfiniteAdelicGroupPoints F G
local notation "Hf" => FiniteAdelicGroupPoints F G
local notation "haar" => (Measure.haar : Measure H)

include hsmooth in
private theorem exists_nonnegative_testFunction :
    ∃ h : H → ℂ, IsAdelicTestFunction F G h ∧ (∀ g, 0 ≤ (h g).re) ∧ 0 < (h 1).re := by
  classical
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  obtain ⟨D, hD, hD₁⟩ := exists_compact_mem_nhds (1 : H∞)
  obtain ⟨bump, hSupport, hSmooth, hNonneg⟩ :=
    isOpen_interior.exists_contMDiff_support_eq (n := (⊤ : ℕ∞)) (𝓘(ℝ, smoothModel F d))
      (s := interior D)
  have hBumpSupp : tsupport bump ⊆ D := closure_minimal (hSupport ▸ interior_subset) hD.isClosed
  let L₀ := FiniteAdelicGroupPoints.compactOpenSubgroup F G
  let L := L₀.toSubgroup
  let h (g : H) : ℂ := if finite F G g ∈ L then (bump (infinite F G g) : ℂ) else 0
  have hOpen : IsOpen {g : H | finite F G g ∈ L} := L₀.isOpen.preimage (finite F G).continuous
  have hClosed : IsClosed {g : H | finite F G g ∈ L} := L₀.isClosed.preimage (finite F G).continuous
  have hCont : Continuous h := by
    let S := {g : H | finite F G g ∈ L}
    have hS : IsClopen S := ⟨hClosed, hOpen⟩
    change Continuous (S.piecewise (fun g => (bump (infinite F G g) : ℂ)) fun _ => 0)
    apply Continuous.piecewise (s := S)
    · simp [hS.frontier_eq]
    · exact Complex.continuous_ofReal.comp (hSmooth.continuous.comp (infinite F G).continuous)
    · exact continuous_const
  have hSlices (b : Hf) : functionInfiniteSlice F G h b ∈ InfinitePlotSmoothFunctions F G := by
    apply (isPlotSmooth_iff_contMDiff F G hsmooth _).mpr
    change ContMDiff 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, ℂ) ∞ (fun a : H∞ => h (pair F G a b))
    by_cases hb : b ∈ L
    · have hReal : ContMDiff 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, ℂ) ∞ (fun a : H∞ => (bump a : ℂ)) :=
        Complex.ofRealCLM.contDiff.contMDiff.comp hSmooth
      simpa only [h, finite_pair, infinite_pair, ite_eq_left hb] using hReal
    · simpa only [h, finite_pair, infinite_pair, ite_eq_right hb] using
        (contMDiff_const (c := (0 : ℂ)) : ContMDiff 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, ℂ) ∞
          (fun _ : H∞ => (0 : ℂ)))
  have hComp : HasCompactSupport h := by
    let E := (split F G).symm '' (D ×ˢ (L : Set Hf))
    have hE : IsCompact E :=
      (hD.prod (FiniteAdelicGroupPoints.isCompact_compactOpenSubgroup F G)).image
        (split F G).symm.continuous
    refine hE.of_isClosed_subset isClosed_closure (closure_minimal ?_ hE.isClosed)
    intro g hg
    have hf : finite F G g ∈ L := by
      by_contra hnot
      exact hg (show h g = 0 by simp only [h, ite_eq_right hnot])
    have hb : bump (infinite F G g) ≠ 0 := by
      intro hh
      apply hg
      simp only [h, ite_eq_left hf, hh, Complex.ofReal_zero]
    exact ⟨(infinite F G g, finite F G g), ⟨hBumpSupp (subset_closure hb), hf⟩, pair_projections F G g⟩
  have hR (l : Hf) (hl : l ∈ L) (g : H) : h (g * ofFinite F G l) = h g := by
    have hiff : finite F G g * l ∈ L ↔ finite F G g ∈ L :=
      ⟨fun h => by simpa only [mul_inv_cancel_right] using L.mul_mem h (L.inv_mem hl),
        fun h => L.mul_mem h hl⟩
    simp only [h, map_mul, infinite_ofFinite, finite_ofFinite, mul_one, hiff]
  have hL (l : Hf) (hl : l ∈ L) (g : H) : h (ofFinite F G l * g) = h g := by
    have hiff : l * finite F G g ∈ L ↔ finite F G g ∈ L :=
      ⟨fun h => by simpa only [inv_mul_cancel_left] using L.mul_mem (L.inv_mem hl) h,
        fun h => L.mul_mem hl h⟩
    simp only [h, map_mul, infinite_ofFinite, finite_ofFinite, one_mul, hiff]
  refine ⟨h, ⟨⟨hCont, hSlices, L, L₀.isOpen, hR⟩, hComp, L, L₀.isOpen, hL⟩,
    fun g => ?_, ?_⟩
  · by_cases hg : finite F G g ∈ L
    · simpa only [h, ite_eq_left hg, Complex.ofReal_re] using hNonneg (infinite F G g)
    · simp only [h, ite_eq_right hg, Complex.zero_re, le_refl]
  · have hf₁ : bump 1 ≠ 0 := by
      change (1 : H∞) ∈ Function.support bump
      rw [hSupport]
      exact mem_interior_iff_mem_nhds.mpr hD₁
    have hLf : finite F G (1 : H) ∈ L := by rw [map_one]; exact L.one_mem
    simpa only [h, ite_eq_left hLf, map_one, Complex.ofReal_re] using lt_of_le_of_ne (hNonneg 1) hf₁.symm

include hsmooth in
private theorem exists_leftCompactInvariant_testFunction
    (K : Subgroup H) (hK : IsMaximalCompactSubgroup F G K) :
    ∃ h : H → ℂ, IsAdelicTestFunction F G h ∧ (∀ k ∈ K, ∀ g, h (k * g) = h g) ∧
      (∫ g, h g ∂haar) ≠ 0 := by
  classical
  obtain ⟨ψ, hψ, hψpos, hψ₁⟩ := exists_nonnegative_testFunction hsmooth
  let D := tsupport ψ
  let C := (K : Set H) * D
  have hC : IsCompact C := hK.1.mul hψ.2.1
  have hS : D ⊆ C := fun g hg => ⟨1, K.one_mem, g, hg, one_mul g⟩
  let b : H → ℂ := C.indicator fun _ => 1
  have hb (k : H) (hk : k ∈ K) (g : H) : b (k * g) = b g := by
    have hm : k * g ∈ C ↔ g ∈ C := by
      constructor
      · rintro ⟨x, hx, y, hy, hxy⟩
        refine ⟨k⁻¹ * x, K.mul_mem (K.inv_mem hk) hx, y, hy, ?_⟩
        change x * y = k * g at hxy
        change (k⁻¹ * x) * y = g
        rw [mul_assoc, hxy, inv_mul_cancel_left]
      · rintro ⟨x, hx, y, hy, rfl⟩
        exact ⟨k * x, K.mul_mem hk hx, y, hy, mul_assoc _ _ _⟩
    unfold b
    rw [Set.indicator_apply, Set.indicator_apply, hm]
  have hbm : Measurable b := measurable_const.indicator hC.isClosed.measurableSet
  have hbi : Integrable b haar := by
    rw [show b = C.indicator (fun _ : H => (1 : ℂ)) from rfl, integrable_indicator_iff hC.isClosed.measurableSet]
    exact integrableOn_const hC.measure_lt_top.ne
  let h := rightConvolution F G ψ b
  obtain ⟨hIntegrable, hSmooth, _⟩ := adelicRightConvolutionDifferentiation F G d hsmooth
    ψ b hψ hbm hbi.locallyIntegrable
  have hInv (k : H) (hk : k ∈ K) (g : H) : h (k * g) = h g := by
    unfold h rightConvolution
    simp_rw [mul_assoc, hb k hk]
  have hSupp : HasCompactSupport h := by
    have hcompact : IsCompact (C * D⁻¹) := hC.mul hψ.2.1.inv
    refine hcompact.of_isClosed_subset isClosed_closure (closure_minimal ?_ hcompact.isClosed)
    intro g hg
    by_contra hnot
    apply hg
    unfold h rightConvolution
    trans ∫ _ : H, (0 : ℂ) ∂haar
    · apply integral_congr_ae
      refine Eventually.of_forall fun a => ?_
      change ψ a * b (g * a) = 0
      by_cases ha : a ∈ D
      · have hna : g * a ∉ C := by
          intro hga
          exact hnot ⟨g * a, hga, a⁻¹, Set.inv_mem_inv.mpr ha, mul_inv_cancel_right g a⟩
        simp only [b, Set.indicator_of_notMem hna, mul_zero]
      · rw [image_eq_zero_of_notMem_tsupport ha, zero_mul]
    · exact integral_zero _ _
  let Kf := K.comap (ofFinite F G).toMonoidHom
  have hKf : IsOpen (Kf : Set Hf) := by
    have heq : Kf = K.map (finite F G).toMonoidHom := by
      ext b
      constructor
      · intro hz
        exact ⟨ofFinite F G b, hz, finite_ofFinite F G b⟩
      · rintro ⟨g, hg, rfl⟩
        exact ((hK.mem_iff g).mp hg).2
    rw [heq]
    exact hK.isOpen_finite
  have hRe (g : H) : 0 ≤ (h g).re := by
    change 0 ≤ (∫ a, ψ a * b (g * a) ∂haar).re
    have ha : (∫ a, (ψ a * b (g * a)).re ∂haar) = (∫ a, ψ a * b (g * a) ∂haar).re :=
      integral_re (hIntegrable g)
    rw [← ha]
    apply integral_nonneg
    intro a
    change 0 ≤ (ψ a * b (g * a)).re
    by_cases ha : g * a ∈ C
    · simpa only [b, Set.indicator_of_mem ha, mul_one] using hψpos a
    · simp only [b, Set.indicator_of_notMem ha, mul_zero, Complex.zero_re, le_refl]
  have hEq : h 1 = ∫ a, ψ a ∂haar := by
    unfold h rightConvolution
    apply integral_congr_ae
    refine Eventually.of_forall fun a => ?_
    change ψ a * b (1 * a) = ψ a
    rw [one_mul]
    by_cases ha : a ∈ D
    · simp only [b, Set.indicator_of_mem (hS ha), mul_one]
    · rw [image_eq_zero_of_notMem_tsupport ha, zero_mul]
  have hAt : 0 < (h 1).re := by
    have hp : (∫ a, (ψ a).re ∂haar) = (∫ a, ψ a ∂haar).re :=
      integral_re (hψ.1.1.integrable_of_hasCompactSupport hψ.2.1)
    rw [hEq, ← hp]
    exact (Complex.continuous_re.comp hψ.1.1).integral_pos_of_hasCompactSupport_nonneg_nonzero
      (hψ.2.1.comp_left Complex.zero_re) hψpos hψ₁.ne'
  refine ⟨h, ⟨hSmooth, hSupp, Kf, hKf, fun l hl => hInv (ofFinite F G l) hl⟩, hInv, ?_⟩
  have hPos : 0 < ∫ a, (h a).re ∂haar :=
    (Complex.continuous_re.comp hSmooth.1).integral_pos_of_hasCompactSupport_nonneg_nonzero
    (hSupp.comp_left Complex.zero_re) hRe hAt.ne'
  have hMassRe : (∫ a, (h a).re ∂haar) = (∫ a, h a ∂haar).re :=
    integral_re (hSmooth.1.integrable_of_hasCompactSupport hSupp)
  rw [hMassRe] at hPos
  exact fun hz => by rw [hz, Complex.zero_re] at hPos; exact (lt_irrefl _ hPos)

private theorem rightConvolution_compact_rightInvariant {f h : H → ℂ}
    {K : Subgroup H} (hh : ∀ k ∈ K, ∀ g, h (k * g) = h g)
    {k : H} (hk : k ∈ K) (g : H) :
    rightConvolution F G h f (g * k) = rightConvolution F G h f g := by
  simpa only [rightConvolution, hh k hk, mul_assoc] using
    integral_mul_left_eq_self («μ» := haar) (fun x => h x * f (g * x)) k

variable {P : GroupScheme (Spec (CommRingCat.of F))} [IsAffine P.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left]

/-- The logarithmic Iwasawa height has smooth infinite slices for any maximal adelic
Iwasawa compact. Smooth averaging preserves its left additive covariance and its
right compact invariance, which determine the pairing up to a constant. -/
theorem IsIwasawaCompact.hasSmoothHeightPairings_of_maximalCompact
    {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K) (hmax : IsMaximalCompactSubgroup F G K) : hK.HasSmoothHeightPairings hsmooth := by
  obtain ⟨h, hh, hInv, hmass⟩ := exists_leftCompactInvariant_testFunction hsmooth K hmax
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  intro lam b
  let f (g : H) := complexParameterPairing F P lam (hK.height g)
  have hf : Continuous f := (continuous_complexParameterPairing lam).comp hK.continuous_height
  let J := rightConvolution F G h f
  obtain ⟨hIntegrable, hSmooth, _⟩ := adelicRightConvolutionDifferentiation F G d hsmooth
    h f hh hf.measurable hf.locallyIntegrable
  let mass := ∫ g, h g ∂haar
  have hm : mass ≠ 0 := hmass
  have hhi : Integrable h haar := hh.1.1.integrable_of_hasCompactSupport hh.2.1
  have hCov (p₀ : AdelicGroupPoints F P) (g : H) :
      f (map F P G p p₀ * g) = complexParameterPairing F P lam (characterLog F P p₀) + f g := by
    dsimp only [f]
    rw [hK.height_map_mul, map_add]
  have hRecovery (g : H) : J g = mass * f g + J 1 := by
    obtain ⟨y, k, hk, hy⟩ := hK.exists_eq g
    have hright : J (map F P G p y * k) = J (map F P G p y) :=
      rightConvolution_compact_rightInvariant hInv hk _
    rw [← hy, hright]
    have hfEq : f (map F P G p y * k) = complexParameterPairing F P lam (characterLog F P y) := by
      rw [hCov]
      simp only [f, hK.height_of_mem hk, map_zero, add_zero]
    rw [hfEq]
    unfold J rightConvolution
    simp_rw [hCov y, mul_add, one_mul, integral_add (hhi.mul_const _) (by
      simpa only [one_mul] using hIntegrable 1), integral_mul_const]
    rfl
  have hJ : ContMDiff 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, ℂ) ∞ (fun a => J (pair F G a b)) :=
    (isPlotSmooth_iff_contMDiff F G hsmooth _).mp (hSmooth.2.1 b)
  change ContMDiff 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, ℂ) ∞ (fun a => f (pair F G a b))
  have haffine : ContDiff ℝ ∞ (fun z : ℂ => mass⁻¹ * (z - J 1)) :=
    contDiff_const.mul (contDiff_id.sub contDiff_const)
  refine (haffine.contMDiff.comp hJ).congr ?_
  intro a
  change f (pair F G a b) = mass⁻¹ * (J (pair F G a b) - J 1)
  rw [hRecovery, add_sub_cancel_right, ← mul_assoc, inv_mul_cancel₀ hm, one_mul]

end Langlands.Global.AdelicGroupPoints

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints

/-- The scalar logarithmic Iwasawa height pairings are smooth on each infinite slice. -/
def AdelicSmoothIwasawaHeightStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G P : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffine P.X.left]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left]
    (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K)
    {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom),
    IsMaximalCompactSubgroup F G K → hK.HasSmoothHeightPairings hsmooth

/-- Apply smooth averaging with the actual adelic Haar measure. -/
theorem adelicSmoothIwasawaHeight : AdelicSmoothIwasawaHeightStatement.{u} := by
  intro F _ _ G P _ _ _ p _ K hK d hsmooth hmax
  exact hK.hasSmoothHeightPairings_of_maximalCompact hsmooth hmax

end Langlands.Global
