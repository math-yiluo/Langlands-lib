import Langlands.Global.AdelicUnipotentArchimedeanRepresentatives
import Langlands.Global.AdelicUnipotentArchimedeanPaths
import Langlands.Global.AdelicStandardConstantTerm
import Langlands.Geometry.Manifold.SmoothGroupConjugation
import Mathlib.Analysis.Calculus.MeanValue

/-! # Bounding deviation from a unipotent constant term by path derivatives -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open AlgebraicGeometry CategoryTheory MeasureTheory NumberField Set
open scoped Classical CategoryTheory.MonObj Manifold ContDiff

namespace Langlands.Geometry.Manifold

section Paths

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {U H : Type*} [Group U] [Group H] [TopologicalSpace U] [TopologicalSpace H]
  [ChartedSpace V U] [ChartedSpace W H]
  [LieGroup 𝓘(ℝ, V) ∞ U] [LieGroup 𝓘(ℝ, W) ∞ H]

local notation "IU" => 𝓘(ℝ, V)
local notation "IH" => 𝓘(ℝ, W)

/-- A path velocity translated to the group identity by left multiplication. -/
def leftPathVelocity (c : ℝ → U) (t : ℝ) : GroupLieAlgebra IU U :=
  mfderiv 𝓘(ℝ, ℝ) IU (fun s : ℝ => (c t)⁻¹ * c s) t (1 : ℝ)

/-- A left path has right-orbit direction given by its translated velocity, mapped into the
ambient Lie algebra and conjugated by the inverse evaluation point. -/
theorem deriv_leftMappedPath (j : U →* H) (hj : ContMDiff IU IH ∞ j)
    (c : ℝ → U) (hc : ContMDiff 𝓘(ℝ, ℝ) IU ∞ c) {f : H → ℂ}
    (hf : ContMDiff IH 𝓘(ℝ, ℂ) ∞ f) (x : H) (t : ℝ) :
    deriv (fun s : ℝ => f (j (c s) * x)) t =
      groupDirectionalValue IH
        (groupTangentConjugation IH x⁻¹ (mfderiv IU IH j 1 (leftPathVelocity c t))) f (j (c t) * x) := by
  let n (s : ℝ) := (c t)⁻¹ * c s
  let k (y : H) := x⁻¹ * y * x
  let b (y : H) := f ((j (c t) * x) * y)
  have hn : ContMDiff 𝓘(ℝ, ℝ) IU ∞ n := contMDiff_const.mul hc
  have hk : ContMDiff IH IH ∞ k := (contMDiff_const.mul contMDiff_id).mul contMDiff_const
  have hb : ContMDiff IH 𝓘(ℝ, ℂ) ∞ b := hf.comp (contMDiff_const.mul contMDiff_id)
  have heq : (fun s : ℝ => f (j (c s) * x)) = b ∘ k ∘ j ∘ n := by
    funext s
    simp only [b, k, n, Function.comp_apply, map_mul, map_inv]
    congr 1
    group
  rw [heq, ← fderiv_apply_one_eq_deriv, ← mvfderiv_eq_fderiv]
  rw [mvfderiv_comp t (hb.mdifferentiableAt (by simp))
    ((hk.comp (hj.comp hn)).mdifferentiableAt (by simp))]
  rw [mfderiv_comp t (hk.mdifferentiableAt (by simp))
    ((hj.comp hn).mdifferentiableAt (by simp))]
  rw [mfderiv_comp t (hj.mdifferentiableAt (by simp)) (hn.mdifferentiableAt (by simp))]
  have hn₁ : n t = 1 := inv_mul_cancel _
  have hj₁ : j (n t) = 1 := by rw [hn₁, map_one]
  have hk₁ : k (j (n t)) = 1 := by simp [k, hj₁]
  change (mvfderiv IH b (k (j (n t))) : W →L[ℝ] ℂ)
    ((mfderiv IH IH k (j (n t)) : W →L[ℝ] W)
      ((mfderiv IU IH j (n t) : V →L[ℝ] W)
        ((mfderiv 𝓘(ℝ, ℝ) IU n t : ℝ →L[ℝ] V) 1))) = _
  rw [hk₁, hj₁, hn₁]
  have he : k = (fun y : H => x⁻¹ * y * (x⁻¹)⁻¹) := by simp [k]
  rw [he]
  rfl

end Paths

end Langlands.Geometry.Manifold

namespace Langlands.Global

open AdelicGroupPoints InfiniteAdelicGroupPoints Langlands.GroupScheme
  Langlands.Geometry.Manifold

variable {F : Type u} [Field F] [NumberField F]
  {G U : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine U.X.left]
  [LocallyOfFiniteType G.X.hom]
  (j : U ⟶ G) [IsClosedImmersion j.hom.hom.left]
  {dU dG : ℕ} (hU : SmoothOfRelativeDimension dU U.X.hom)
  (hG : SmoothOfRelativeDimension dG G.X.hom)

local notation "A" => AdelicGroupPoints F G
local notation "Gf" => FiniteAdelicGroupPoints F G
local notation "G∞" => InfiniteAdelicGroupPoints F G
local notation "U∞" => InfiniteAdelicGroupPoints F U
local notation "IU" => 𝓘(ℝ, smoothModel F dU)
local notation "IG" => 𝓘(ℝ, smoothModel F dG)
local notation "j∞" => U.affinePointsTarget j (CommAlgCat.of F (InfiniteAdeleRing F))
local notation "m" => map F U G j
local notation "V" => SubgroupFunctor.range j
local notation "Q" => AdelicSubgroupPoints.RationalQuotient F G V
local notation "Γ" => AdelicSubgroupPoints.rationalSubgroup F G V
local notation "ν" => AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G V

/-- At a fixed finite level, a uniform path derivative bound controls the departure of a
function from its value averaged over the rational unipotent quotient. -/
def AdelicUnipotentConstantTermOscillationStatement : Prop :=
  ConnectedSpace U.X.left → IsUnipotent U →
  ∀ (Yf : Set Gf), IsCompact Yf → ∀ (L : Subgroup Gf), IsOpen (L : Set Gf) →
  letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F U hU
  letI := smoothChartedSpace F G hG
  letI := smoothLieGroup F U hU
  letI := smoothLieGroup F G hG
  ∃ D : Set U∞, IsCompact D ∧ ∃ p : U∞ × ℝ → U∞,
    ContMDiff (ModelWithCorners.prod IU 𝓘(ℝ, ℝ)) IU ∞ p ∧
    (∀ u : U∞, p (u, 0) = 1) ∧ (∀ u : U∞, p (u, 1) = u) ∧
    ∀ (f : A → ℂ), Continuous f →
    (∀ b : Gf, ContMDiff IG 𝓘(ℝ, ℂ) ∞ (fun y : G∞ => f (pair F G y b))) →
    (∀ (q : RationalGroupPoints F U) x, f (m (rational F U q) * x) = f x) →
    (∀ l ∈ L, ∀ x, f (x * ofFinite F G l) = f x) →
    ∀ x : A, finite F G x ∈ Yf → ∀ B : ℝ,
    (∀ u ∈ D, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖groupDirectionalValue IG
        (groupTangentConjugation IG (infinite F G x)⁻¹
          (mfderiv IU IG j∞ 1 (leftPathVelocity (fun s => p (u, s)) t)))
        (fun y : G∞ => f (pair F G y (finite F G x))) (j∞ (p (u, t)) * infinite F G x)‖ ≤ B) →
    ‖f x - subgroupConstantTerm F j f x‖ ≤ B

theorem adelicUnipotentConstantTermOscillation :
    AdelicUnipotentConstantTermOscillationStatement j hU hG := by
  intro hconn hu Yf hY L hL
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F U hU
  let := smoothChartedSpace F G hG
  let := smoothLieGroup F U hU
  let := smoothLieGroup F G hG
  let : Smooth U.X.hom := hU.smooth
  obtain ⟨D, hD, hrep⟩ := adelicUnipotentArchimedeanRepresentatives j hconn hu Yf hY L hL
  obtain ⟨p, hp, hp₀, hp₁⟩ := adelicUnipotentArchimedeanPaths hU hconn hu
  have hj : ContMDiff IU IG ∞ j∞ := by
    apply (contMDiff_iff_coordinateSmooth F G IU hG _).mpr
    exact ((contMDiff_iff_coordinateSmooth F U IU hU id).mp contMDiff_id).postcomp j.hom.hom
  have hmapInf (a : U∞) : m (ofInfinite F U a) = ofInfinite F G (j∞ a) := by
    have hi (z : AdelicGroupPoints F U) : infinite F G (m z) = j∞ (infinite F U z) :=
      DFunLike.congr_fun (U.affinePointsTarget_naturality j
        (CommAlgCat.ofHom (AlgHom.fst F (InfiniteAdeleRing F) (FiniteAdeles F)))) z
    apply (split F G).injective
    simp only [split_apply, hi, finite_map, infinite_ofInfinite, finite_ofInfinite, map_one]
  let : IsClosed (AdelicSubgroupPoints.adelicPoints F G V : Set A) :=
    AdelicSubgroupPoints.isClosed_adelicPoints_range F G j
  let : CompactSpace Q := AdelicSubgroupPoints.compactSpace_rationalQuotient_range_unipotent F j hU.smooth hconn hu
  let : BorelSpace Q := AdelicSubgroupPoints.rationalQuotientBorelSpace F G V
  let : IsProbabilityMeasure ν := AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G V
  refine ⟨D, hD, p, hp, hp₀, hp₁, ?_⟩
  intro f hf hfInf hfQ hfL x hx B hB
  let a (q : Q) := f ((Quotient.out q : AdelicSubgroupPoints.adelicPoints F G V).val * x)
  let phi := LeftCosetSpace.lift Γ
    (fun y : AdelicSubgroupPoints.adelicPoints F G V => f (y.val * x))
    (fun r y => by
      obtain ⟨r₀, hr₀⟩ := (mem_rationalSubgroup_range_iff j r.val).mp r.2
      change f ((r.val.val * y.val) * x) = _
      rw [← hr₀, mul_assoc]
      exact hfQ r₀ (y.val * x))
  have hphi : Continuous phi :=
    (LeftCosetSpace.continuous_iff Γ).mpr (hf.comp (continuous_subtype_val.mul continuous_const))
  have ha_eq : a = phi := funext fun q => congrArg phi (Quotient.out_eq q)
  have hai : Integrable a ν := ha_eq ▸ hphi.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hdiff (u : U∞) (huD : u ∈ D) : ‖f (m (ofInfinite F U u) * x) - f x‖ ≤ B := by
    let c (s : ℝ) := p (u, s)
    let fInf (y : G∞) := f (pair F G y (finite F G x))
    have hc : ContMDiff 𝓘(ℝ, ℝ) IU ∞ c := hp.comp (contMDiff_const.prodMk contMDiff_id)
    have hfInf' : ContMDiff IG 𝓘(ℝ, ℂ) ∞ fInf := hfInf _
    let k (s : ℝ) := fInf (j∞ (c s) * infinite F G x)
    have hk : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ k := hfInf'.comp ((hj.comp hc).mul contMDiff_const)
    have hk₀ : k 0 = f x := by simp [k, c, fInf, hp₀]
    have hk₁ : k 1 = f (m (ofInfinite F U u) * x) := by
      rw [hmapInf, ofInfinite_eq_pair, pair_mul_right, one_mul]
      simp [k, c, fInf, hp₁]
    rw [← hk₀, ← hk₁]
    apply norm_image_sub_le_of_norm_deriv_le_segment_01' (f' := deriv k)
      (fun t _ => ((hk.contDiff.differentiable (by simp)).differentiableAt (x := t)).hasDerivAt.hasDerivWithinAt)
    intro t ht
    change ‖deriv (fun s : ℝ => fInf (j∞ (c s) * infinite F G x)) t‖ ≤ B
    rw [deriv_leftMappedPath j∞ hj c hc hfInf']
    exact hB u huD t (Ico_subset_Icc_self ht)
  have hbound (q : Q) : ‖f x - a q‖ ≤ B := by
    obtain ⟨u, huq⟩ := AdelicSubgroupPoints.adelicRangeMap_surjective F j (Quotient.out q)
    have he : m u = (Quotient.out q : AdelicSubgroupPoints.adelicPoints F G V).val := congrArg Subtype.val huq
    obtain ⟨v, hv, r, h⟩ := hrep u
    obtain ⟨l, hl⟩ := h x hx
    have hqv : a q = f (m (ofInfinite F U v) * x) := by
      change f ((Quotient.out q : AdelicSubgroupPoints.adelicPoints F G V).val * x) = _
      rw [← he, ← hfQ r (m u * x), hl, hfL l.val l.property]
    rw [hqv, norm_sub_rev]
    exact hdiff v hv
  change ‖f x - ∫ q, a q ∂ν‖ ≤ B
  have hc : (∫ _ : Q, f x ∂ν) = f x := by simp
  rw [← hc, ← integral_sub (integrable_const _) hai]
  exact (norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall hbound)).trans_eq (by simp)

end Langlands.Global
