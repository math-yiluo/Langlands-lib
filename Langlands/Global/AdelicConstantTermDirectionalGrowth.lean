import Langlands.Global.AdelicMaximalUnipotentDecay
import Langlands.Global.AdelicCompactConstantTermCovariance

/-! # Uniform growth of derivatives after taking a unipotent constant term -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

open AlgebraicGeometry CategoryTheory Filter MeasureTheory NumberField Set Topology
open scoped Classical CategoryTheory.MonObj Manifold ContDiff

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints InfiniteAdelicGroupPoints
  Langlands.Geometry.Manifold RepresentationGrowth

variable {F : Type u} [Field F] [NumberField F]
  {G U : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffine U.X.left]
  (j : U ⟶ G) [IsClosedImmersion j.hom.hom.left]
  {d N : ℕ} (hG : SmoothOfRelativeDimension d G.X.hom) (rho : MatrixRepresentation G (Fin N))

local notation "W" => smoothModel F d
local notation "IG" => 𝓘(ℝ, W)
local notation "IC" => 𝓘(ℝ, ℂ)
local notation "A" => AdelicGroupPoints F G
local notation "Gf" => FiniteAdelicGroupPoints F G
local notation "G∞" => InfiniteAdelicGroupPoints F G
local notation "V" => SubgroupFunctor.range j
local notation "Uₐ" => AdelicSubgroupPoints.adelicPoints F G V
local notation "Q" => AdelicSubgroupPoints.RationalQuotient F G V
local notation "Γ" => AdelicSubgroupPoints.rationalSubgroup F G V
local notation "ν" => AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G V
local notation "mU" => map F U G j
local notation "CT" => subgroupConstantTerm F j
local notation "height" => adelicHeight F G rho

/-- A continuous function with left rational unipotent invariance has a continuous
normalized unipotent constant term. -/
theorem continuous_subgroupConstantTerm_of_unipotentInvariant
    (hU : Smooth U.X.hom) (hconn : ConnectedSpace U.X.left) (hu : IsUnipotent U)
    (f : A → ℂ) (hf : Continuous f)
    (hfR : ∀ (q : RationalGroupPoints F U) x, f (mU (rational F U q) * x) = f x) :
    Continuous (CT f) := by
  let : IsClosed (Uₐ : Set A) := AdelicSubgroupPoints.isClosed_adelicPoints_range F G j
  let : CompactSpace Q := AdelicSubgroupPoints.compactSpace_rationalQuotient_range_unipotent F j hU hconn hu
  let : BorelSpace Q := AdelicSubgroupPoints.rationalQuotientBorelSpace F G V
  let : IsProbabilityMeasure ν := AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G V
  let J (g : A) : Q → ℂ := LeftCosetSpace.lift Γ (fun u : Uₐ => f (u.val * g)) (fun r u => by
    obtain ⟨q, hq⟩ := (mem_rationalSubgroup_range_iff j r.val).mp r.2
    change mU (rational F U q) = r.val.val at hq
    change f ((r.val.val * u.val) * g) = _
    rw [← hq, mul_assoc, hfR q])
  have hJ : Continuous (fun p : A × Q => J p.1 p.2) := by
    rw [← (IsOpenQuotientMap.id.prodMap (LeftCosetSpace.isOpenQuotientMap_mk Γ)).continuous_comp_iff]
    exact hf.comp ((continuous_subtype_val.comp continuous_snd).mul continuous_fst)
  have heq : CT f = fun g => ∫ z : Q, J g z ∂ν := by
    funext g
    change (∫ z : Q, f ((Quotient.out z : Uₐ).val * g) ∂ν) = _
    exact integral_congr_ae (Eventually.of_forall fun q => congrArg (J g) (Quotient.out_eq q))
  rw [heq]
  simpa only [Measure.restrict_univ] using
    (continuous_parametric_integral_of_continuous («μ» := ν) hJ isCompact_univ)

/-- A uniform growth exponent for all right-orbit derivatives is preserved by the
actual normalized unipotent constant term, with the same family size factor. -/
def AdelicConstantTermDirectionalGrowthStatement : Prop :=
  Smooth U.X.hom → ConnectedSpace U.X.left → IsUnipotent U → 0 < N →
  letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hG
  ∀ (L : Subgroup Gf), IsOpen (L : Set Gf) →
  ∀ (I : Type v) (f : I → A → ℂ) (size : I → ℝ), (∀ q, 0 ≤ size q) →
  (∀ q, Continuous (f q)) →
  (∀ q (b : Gf), ContMDiff IG IC ∞ (fun y : G∞ => f q (pair F G y b))) →
  (∀ q (r : RationalGroupPoints F U) x, f q (mU (rational F U r) * x) = f q x) →
  (∀ q, ∀ l ∈ L, ∀ x, f q (x * ofFinite F G l) = f q x) →
  ∀ R : ℝ, 0 ≤ R →
  (∀ s : List W, ∃ C : ℝ, 0 ≤ C ∧
    ∀ q x, ‖adelicIteratedDirectionalValue hG s (f q) x‖ ≤ C * height x ^ R * size q) →
  (∀ q, Continuous (CT (f q))) ∧
  (∀ q (b : Gf), ContMDiff IG IC ∞ (fun y : G∞ => CT (f q) (pair F G y b))) ∧
  (∀ q, ∀ l ∈ L, ∀ x, CT (f q) (x * ofFinite F G l) = CT (f q) x) ∧
  (∀ q s, adelicIteratedDirectionalValue hG s (CT (f q)) = CT (adelicIteratedDirectionalValue hG s (f q))) ∧
  (∀ s : List W, ∃ C : ℝ, 0 ≤ C ∧
    ∀ q x, ‖adelicIteratedDirectionalValue hG s (CT (f q)) x‖ ≤ C * height x ^ R * size q)

theorem adelicConstantTermDirectionalGrowth :
    AdelicConstantTermDirectionalGrowthStatement.{u, v} j hG rho := by
  intro hU hconn hu hN
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hG
  intro L hL I f size hsize hf hfS hfR hfL R hR hgrow
  have hDiff q := adelicUnipotentConstantTermDifferentiation j hG hU hconn hu L hL (f q)
    (hf q) (hfS q) (hfR q) (hfL q)
  have hiter (q : I) (s : List W) :
      let g := adelicIteratedDirectionalValue hG s (f q)
      (Continuous g ∧
        (∀ b : Gf, ContMDiff IG IC ∞ (fun y : G∞ => g (pair F G y b))) ∧
        (∀ (r : RationalGroupPoints F U) x, g (mU (rational F U r) * x) = g x) ∧
        (∀ l ∈ L, ∀ x, g (x * ofFinite F G l) = g x)) ∧
      adelicIteratedDirectionalValue hG s (CT (f q)) = CT g := by
    induction s with
    | nil =>
      exact ⟨⟨hf q, hfS q, hfR q, hfL q⟩, rfl⟩
    | cons X s ih =>
      obtain ⟨⟨hg, hgS, hgR, hgL⟩, heq⟩ := ih
      let g := adelicIteratedDirectionalValue hG s (f q)
      have hd := adelicUnipotentConstantTermDifferentiation j hG hU hconn hu L hL g hg hgS hgR hgL
      simp only [adelicIteratedDirectionalValue_cons]
      refine ⟨hd.1 X, ?_⟩
      rw [heq]
      funext x
      rw [← pair_projections F G x, adelicDirectionalValue_pair]
      exact ((hd.2 (finite F G x)).2 X (infinite F G x))
  refine ⟨fun q => continuous_subgroupConstantTerm_of_unipotentInvariant j hU hconn hu _ (hf q) (hfR q),
    fun q b => ((hDiff q).2 b).1, ?_, fun q s => (hiter q s).2, ?_⟩
  · intro q l hl x
    apply integral_congr_ae
    exact Eventually.of_forall (fun u => by
      change f q ((Quotient.out u : Uₐ).val * (x * ofFinite F G l)) =
        f q ((Quotient.out u : Uₐ).val * x)
      rw [← mul_assoc, hfL q l hl])
  · let : IsClosed (Uₐ : Set A) := AdelicSubgroupPoints.isClosed_adelicPoints_range F G j
    let : LocallyCompactSpace Uₐ := (show IsClosed (Uₐ : Set A) from inferInstance).locallyCompactSpace
    let : CompactSpace Q := AdelicSubgroupPoints.compactSpace_rationalQuotient_range_unipotent F j hU hconn hu
    let : BorelSpace Q := AdelicSubgroupPoints.rationalQuotientBorelSpace F G V
    let : IsProbabilityMeasure ν := AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G V
    obtain ⟨K, hK, hKcov⟩ := EisensteinConstantTerm.exists_isCompact_mul_mem Γ
    obtain ⟨B, hB⟩ := (hK.image ((continuous_adelicHeight F G rho hN).comp continuous_subtype_val)).bddAbove
    let B' := max 1 B
    have hB' : 0 ≤ B' := zero_le_one.trans (le_max_left _ _)
    intro s
    obtain ⟨C, hC, hCs⟩ := hgrow s
    refine ⟨C * B' ^ R, mul_nonneg hC (Real.rpow_nonneg hB' _), fun q x => ?_⟩
    let g := adelicIteratedDirectionalValue hG s (f q)
    rw [(hiter q s).2]
    change ‖∫ z : Q, g ((Quotient.out z : Uₐ).val * x) ∂ν‖ ≤ _
    refine (norm_integral_le_of_norm_le_const (C := C * B' ^ R * height x ^ R * size q)
      (Eventually.of_forall fun z => ?_)).trans_eq (by simp)
    obtain ⟨r, hr, u, huK, hru⟩ := hKcov (Quotient.out z)
    obtain ⟨r₀, hr₀⟩ := (mem_rationalSubgroup_range_iff j r).mp hr
    change mU (rational F U r₀) = r.val at hr₀
    have hInv : g (mU (rational F U r₀) * (u.val * x)) = g (u.val * x) :=
      (hiter q s).1.2.2.1 r₀ (u.val * x)
    rw [hru, Subgroup.coe_mul, ← hr₀, mul_assoc, hInv]
    have huB : height u.val ≤ B' := (hB ⟨u, huK, rfl⟩).trans (le_max_right _ _)
    have hH : height (u.val * x) ≤ B' * height x :=
      (adelicHeight_mul_le F G rho hN _ _).trans
        (mul_le_mul_of_nonneg_right huB (zero_le_one.trans (one_le_adelicHeight F G rho hN x)))
    calc
      ‖g (u.val * x)‖ ≤ C * height (u.val * x) ^ R * size q := hCs q _
      _ ≤ C * (B' * height x) ^ R * size q :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (zero_le_one.trans (one_le_adelicHeight F G rho hN _)) hH hR) hC) (hsize q)
      _ = C * B' ^ R * height x ^ R * size q := by
        rw [Real.mul_rpow hB' (zero_le_one.trans (one_le_adelicHeight F G rho hN x))]
        ring

end Langlands.Global
