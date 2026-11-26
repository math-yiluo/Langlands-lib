import Langlands.Global.AdelicCompactEnvelopingIntegral
import Langlands.Global.AdelicGroupLocalPoints
import Langlands.Global.AdelicTwistedConvolutionFibres

/-! # Levi fibre differential equations under transported right convolution -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory MeasureTheory NumberField Set
open scoped Classical CategoryTheory.MonObj ContDiff Manifold

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.Global.AdelicGroupPoints

open InfiniteAdelicGroupPoints Langlands.Automorphic.GroupSchemeFunctions

variable {F : Type u} [Field F] [NumberField F]
  {G M : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine M.X.left]

local notation "A" => AdelicGroupPoints F G
local notation "G∞" => InfiniteAdelicGroupPoints F G
local notation "M∞" => InfiniteAdelicGroupPoints F M
local notation "Af" => FiniteAdelicGroupPoints F G
local notation "μ" => (Measure.haar : Measure A)
local notation "Iℂ" => 𝓘(ℝ, ℂ)
local notation "R∞" => CommAlgCat.of F (InfiniteAdeleRing F)

/-- Restriction of a smooth infinite adelic slice to the subgroup fibre through an
adelic base point. -/
def subgroupFibreSmoothSlice (j : M ⟶ G) (f : A → ℂ)
    (hf : ∀ b, functionInfiniteSlice F G f b ∈ InfinitePlotSmoothFunctions F G)
    (x : A) : InfinitePlotSmoothFunctions F M :=
  let sx : InfinitePlotSmoothFunctions F G := ⟨functionInfiniteSlice F G f (finite F G x), hf _⟩
  ⟨fun m => sx.val (M.affinePointsTarget j R∞ m * infinite F G x),
    (GroupScheme.IsPlotSmooth.rightTranslate G R∞ (B := mixedEmbedding.mixedSpace F)
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom sx.property (infinite F G x)).postcomp
      j.hom.hom⟩

/-- Evaluation on the fibre is evaluation of the original adelic function after left
multiplication by the included infinite subgroup point. -/
theorem subgroupFibreSmoothSlice_apply (j : M ⟶ G) (f : A → ℂ)
    (hf : ∀ b, functionInfiniteSlice F G f b ∈ InfinitePlotSmoothFunctions F G)
    (x : A) (m : M∞) :
    (subgroupFibreSmoothSlice j f hf x).val m = f (map F M G j (ofInfinite F M m) * x) := by
  change f (pair F G (M.affinePointsTarget j R∞ m * infinite F G x) (finite F G x)) = _
  rw [map_ofInfinite, ofInfinite_eq_pair]
  conv_rhs => rw [← pair_projections F G x]
  rw [pair_mul, one_mul]

variable [LocallyOfFiniteType G.X.hom] {P : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine P.X.left] {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left]
variable {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K)
  {d e : ℕ} (hsG : SmoothOfRelativeDimension d G.X.hom) (hsM : SmoothOfRelativeDimension e M.X.hom)
  (hcM : AdelicDifferentialCommutator F M hsM)

local notation "IM" => 𝓘(ℝ, smoothModel F e)
local notation "IG" => 𝓘(ℝ, smoothModel F d)
local notation "D" => plotSmoothEnvelopingAction F M hsM hcM

/-- For a kernel localized at a fixed finite level of the input, an enveloping derivative
of the transported convolution on a Levi fibre is the integral of the derivatives of the
translated input fibres. -/
theorem IsIwasawaCompact.twistedConvolutionEnd_fibreEnveloping
    (l : M ⟶ P) (hH : hK.HasSmoothHeightPairings hsG)
    (L : Subgroup Af) {h : A → ℂ} (hh : IsAdelicTestFunction F G h)
    (hL : ∀ t, h t ≠ 0 → finite F G t ∈ L)
    (lam : ComplexCharacterParameter F P) (f : C(A, ℂ))
    (hf : ∀ b, functionInfiniteSlice F G f b ∈ InfinitePlotSmoothFunctions F G)
    (hfL : ∀ b ∈ L, ∀ x, f (x * ofFinite F G b) = f x)
    (z : AdelicEnvelopingAlgebra F M hsM) (x : A) (m : M∞) :
    (D z (subgroupFibreSmoothSlice (l ≫ p) (hK.twistedConvolutionEnd hsG hh lam f)
      (hK.twistedConvolutionEnd_smoothSlice hsG hH hh lam f) x)).val m =
      ∫ t, hK.parabolicFibreKernel h lam x t *
        (D z (subgroupFibreSmoothSlice (l ≫ p) f hf (x * t))).val m ∂μ := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsG
  let := smoothChartedSpace F M hsM
  let := smoothLieGroup F G hsG
  let : IsManifold IG ∞ G∞ := smoothIsManifold F G hsG
  let includeInfinite : M∞ → G∞ := M.affinePointsTarget (l ≫ p) R∞
  let w := hK.parabolicFibreKernel h lam x
  have hw := hK.continuous_parabolicFibreKernel hh.1.1 lam x
  have hw₀ (t : A) (ht : t ∉ tsupport h) : w t = 0 := by
    unfold w IsIwasawaCompact.parabolicFibreKernel
    rw [image_eq_zero_of_notMem_tsupport ht, zero_mul]
  have hincludeInfinite : ContMDiff IM IG ∞ includeInfinite := by
    apply (contMDiff_iff_coordinateSmooth F G IM hsG _).mpr
    exact ((contMDiff_iff_coordinateSmooth F M IM hsM id).mp contMDiff_id).postcomp (l ≫ p).hom.hom
  let b := finite F G x
  let a := infinite F G x
  let family (q : M∞ × G∞) := f (pair F G (includeInfinite q.1 * (a * q.2)) b)
  have hFamily : ContMDiff ((IM).prod IG) Iℂ ∞ family :=
    ((isPlotSmooth_iff_contMDiff F G hsG (functionInfiniteSlice F G f b)).mp (hf b)).comp
      ((hincludeInfinite.comp contMDiff_fst).mul (contMDiff_const.mul contMDiff_snd))
  let T := tsupport h
  have hT : IsCompact T := hh.2.1.isCompact
  have hTm : MeasurableSet T := hT.isClosed.measurableSet
  let : CompactSpace T := isCompact_iff_compactSpace.mp hT
  let ν := (μ).comap (Subtype.val : T → A)
  let : IsFiniteMeasure ν := ⟨by
    dsimp only [ν]
    rw [(MeasurableEmbedding.subtype_coe hTm).comap_apply, Set.image_univ, Subtype.range_coe]
    exact hT.measure_lt_top⟩
  let w' : C(T, ℂ) := ⟨fun t => w t.val, hw.comp continuous_subtype_val⟩
  let j' : C(T, G∞) := ⟨fun t => infinite F G t.val, (infinite F G).continuous.comp continuous_subtype_val⟩
  have hvals (t : A) (ht : finite F G t ∈ L) (y : M∞) :
      (subgroupFibreSmoothSlice (l ≫ p) f hf (x * t)).val y = family (y, infinite F G t) := by
    rw [subgroupFibreSmoothSlice_apply, map_ofInfinite, ← pair_projections F G (x * t)]
    simp only [ofInfinite_eq_pair, pair_mul, one_mul, map_mul]
    have heq : pair F G (includeInfinite y * (a * infinite F G t)) (b * finite F G t) =
        pair F G (includeInfinite y * (a * infinite F G t)) b * ofFinite F G (finite F G t) := by
      rw [ofFinite_eq_pair, pair_mul, mul_one]
    exact (congrArg f heq).trans (hfL _ ht _)
  have hfamilySlice (t : A) (ht : finite F G t ∈ L) :
      subgroupFibreSmoothSlice (l ≫ p) f hf (x * t) =
        plotSmoothFamilySlice (H := smoothModel F d) hsM family hFamily (infinite F G t) :=
    Subtype.ext (funext (hvals t ht))
  let integrated := compactIntegralPlotSmooth (H := smoothModel F d) hsM ν w' j' family hFamily
  have hIntegrated : subgroupFibreSmoothSlice (l ≫ p) (hK.twistedConvolutionEnd hsG hh lam f)
      (hK.twistedConvolutionEnd_smoothSlice hsG hH hh lam f) x = integrated := by
    apply Subtype.ext
    funext y
    rw [subgroupFibreSmoothSlice_apply, map_comp_apply_of_hom l,
      hK.twistedConvolutionEnd_map_mul]
    change (∫ t, w t * f (map F P G p (map F M P l (ofInfinite F M y)) * (x * t)) ∂μ) =
      ∫ t : T, w t.val * family (y, infinite F G t.val) ∂ν
    have he : (∫ t, w t * f (map F P G p (map F M P l (ofInfinite F M y)) * (x * t)) ∂μ) =
        ∫ t, w t * family (y, infinite F G t) ∂μ := by
      apply integral_congr_ae
      filter_upwards with t
      by_cases ht : h t = 0
      · simp only [w, IsIwasawaCompact.parabolicFibreKernel, ht, zero_mul]
      · rw [← map_comp_apply_of_hom l, ← subgroupFibreSmoothSlice_apply (l ≫ p) f hf]
        rw [hvals t (hL t ht)]
    rw [he]
    dsimp only [ν]
    rw [integral_subtype_comap hTm (fun t => w t * family (y, infinite F G t))]
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    rw [hw₀ t ht, zero_mul]
  rw [hIntegrated]
  rw [compactIntegralPlotSmooth_enveloping (H := smoothModel F d)]
  change (∫ t : T, w t.val * (D z (plotSmoothFamilySlice (H := smoothModel F d) hsM family hFamily
    (infinite F G t.val))).val m ∂ν) = _
  dsimp only [ν]
  rw [integral_subtype_comap hTm (fun t => w t *
    (D z (plotSmoothFamilySlice (H := smoothModel F d) hsM family hFamily
      (infinite F G t))).val m)]
  have heq : (∫ t in T, w t * (D z (plotSmoothFamilySlice (H := smoothModel F d) hsM family hFamily
      (infinite F G t))).val m ∂μ) =
    ∫ t in T, w t * (D z (subgroupFibreSmoothSlice (l ≫ p) f hf (x * t))).val m ∂μ := by
    apply integral_congr_ae
    filter_upwards with t
    by_cases ht : h t = 0
    · simp only [w, IsIwasawaCompact.parabolicFibreKernel, ht, zero_mul]
    · rw [hfamilySlice t (hL t ht)]
  rw [heq]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro t ht
  rw [hw₀ t ht, zero_mul]

end Langlands.Global.AdelicGroupPoints
