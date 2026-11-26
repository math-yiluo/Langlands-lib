import Langlands.Analysis.CompactManifoldVectorIntegral
import Langlands.Automorphic.GroupSchemeAdelicUniformGrowth

/-! # Compact weighted integration of actual enveloping derivatives -/

noncomputable section

universe u v w r

open AlgebraicGeometry Bundle CategoryTheory MeasureTheory NumberField
open scoped CategoryTheory.MonObj ContDiff Manifold TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.Global.InfiniteAdelicGroupPoints

open Langlands.Analysis Langlands.Automorphic.GroupSchemeFunctions Langlands.Geometry.Manifold

private theorem contMDiff_firstGroupDirectionalValue
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {M : Type*} [TopologicalSpace M] [ChartedSpace V M] [Group M] [LieGroup 𝓘(ℝ, V) ∞ M]
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold 𝓘(ℝ, H) ∞ N]
    (X : V) {f : M × N → ℂ} (hf : ContMDiff (𝓘(ℝ, V).prod 𝓘(ℝ, H)) 𝓘(ℝ, ℂ) ∞ f) :
    ContMDiff (𝓘(ℝ, V).prod 𝓘(ℝ, H)) 𝓘(ℝ, ℂ) ∞
      (fun p : M × N => groupDirectionalValue 𝓘(ℝ, V) X (fun y => f (y, p.2)) p.1) := by
  let g (p : (M × N) × M) := f (p.1.1 * p.2, p.1.2)
  have hg : ContMDiff ((𝓘(ℝ, V).prod 𝓘(ℝ, H)).prod 𝓘(ℝ, V)) 𝓘(ℝ, ℂ) ∞ g :=
    hf.comp (((contMDiff_fst.comp contMDiff_fst).mul contMDiff_snd).prodMk
      (contMDiff_snd.comp contMDiff_fst))
  intro p₀
  have hd := (hg.contMDiffAt (x := (p₀, (1 : M)))).mfderiv_apply (m := ∞) (x₀ := p₀)
    (fun p y => g (p, y)) (fun _ : M × N => (1 : M))
    (fun p : M × N => p) (fun _ : M × N => X)
    contMDiffAt_const contMDiffAt_id contMDiffAt_const (by simp)
  have hc (p : M × N) : inTangentCoordinates 𝓘(ℝ, V) 𝓘(ℝ, ℂ)
      (fun _ : M × N => (1 : M)) (fun p : M × N => g (p, 1))
      (fun p : M × N => mfderiv 𝓘(ℝ, V) 𝓘(ℝ, ℂ) (fun y => g (p, y)) 1) p₀ p =
        mfderiv 𝓘(ℝ, V) 𝓘(ℝ, ℂ) (fun y => g (p, y)) 1 := by
    rw [inTangentCoordinates_eq]
    · rw [tangentBundleCore_coordChange_model_space]
      have he : (tangentBundleCore 𝓘(ℝ, V) M).coordChange
          (achart V (1 : M)) (achart V (1 : M)) 1 = ContinuousLinearMap.id ℝ V := by
        ext Y
        exact tangentCoordChange_self (mem_extChartAt_source (I := 𝓘(ℝ, V)) (1 : M))
      rw [he, ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]
    · exact mem_chart_source V (1 : M)
    · simp
  simp_rw [hc] at hd
  exact hd

private theorem complexEnveloping_real_left_induction {L : Type*} [LieRing L] [LieAlgebra ℝ L]
    {T : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] L) → Prop}
    (h1 : T 1) (hadd : ∀ a b, T a → T b → T (a + b))
    (hsmul : ∀ (c : ℂ) a, T a → T (c • a))
    (hgen : ∀ (X : L) a, T a → T (UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X) * a))
    (a : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] L)) : T a := by
  have hcomplex (X : ℂ ⊗[ℝ] L) : ∀ b, T b → T (UniversalEnvelopingAlgebra.ι ℂ X * b) := by
    induction X using TensorProduct.inductionOn with
    | tmul c X =>
      intro b hb
      have he : c ⊗ₜ[ℝ] X = c • ((1 : ℂ) ⊗ₜ[ℝ] X) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [he, map_smul, smul_mul_assoc]
      exact hsmul c _ (hgen X b hb)
    | add X Y hX hY =>
      intro b hb
      rw [map_add, add_mul]
      exact hadd _ _ (hX b hb) (hY b hb)
  obtain ⟨t, rfl⟩ := RingCon.mkₐ_surjective (α := ℂ)
    (UniversalEnvelopingAlgebra.ringCon ℂ (ℂ ⊗[ℝ] L)) a
  let q := UniversalEnvelopingAlgebra.mkAlgHom ℂ (ℂ ⊗[ℝ] L)
  have hq (s : TensorAlgebra ℂ (ℂ ⊗[ℝ] L)) : ∀ b, T b → T (q s * b) := by
    induction s using TensorAlgebra.induction with
    | algebraMap c =>
      intro b hb
      rw [AlgHom.commutes, ← Algebra.smul_def]
      exact hsmul _ _ hb
    | «ι» X => exact hcomplex X
    | mul s t hs ht =>
      intro b hb
      rw [map_mul, mul_assoc]
      exact hs _ (ht _ hb)
    | add s t hs ht =>
      intro b hb
      rw [map_add, add_mul]
      exact hadd _ _ (hs _ hb) (ht _ hb)
  change T (q t)
  simpa only [mul_one] using hq t 1 h1

variable {F : Type u} [Field F] [NumberField F]
  {M : GroupScheme (Spec (CommRingCat.of F))} [IsAffine M.X.left]
  {d : ℕ} (hsmooth : SmoothOfRelativeDimension d M.X.hom)
  (hcalc : AdelicDifferentialCommutator F M hsmooth)

local notation "M∞" => InfiniteAdelicGroupPoints F M
local notation "IM" => 𝓘(ℝ, smoothModel F d)
local notation "Iℂ" => 𝓘(ℝ, ℂ)
local notation "S" => InfinitePlotSmoothFunctions F M
local notation "U" => AdelicEnvelopingAlgebra F M hsmooth
local notation "D" => plotSmoothEnvelopingAction F M hsmooth hcalc

variable {X : Type v} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    {H : Type w} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {N : Type r} [TopologicalSpace N] [ChartedSpace H N] [IsManifold 𝓘(ℝ, H) ∞ N]
    (measure : Measure X) [IsFiniteMeasure measure] (wgt : C(X, ℂ)) (j : C(X, N))

/-- Integrate a jointly smooth family of infinite adelic functions against a continuous
weight on a compact space before applying the actual enveloping action. -/
def compactIntegralPlotSmooth :
    let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    let := smoothChartedSpace F M hsmooth
    ∀ (f : M∞ × N → ℂ), ContMDiff ((IM).prod 𝓘(ℝ, H)) Iℂ ∞ f → S := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F M hsmooth
  let := smoothLieGroup F M hsmooth
  let : IsManifold IM ∞ M∞ := smoothIsManifold F M hsmooth
  dsimp only
  intro f hf
  refine ⟨fun m => ∫ x, wgt x * f (m, j x) ∂measure, ?_⟩
  apply (isPlotSmooth_iff_contMDiff F M hsmooth
    (fun m => ∫ x, wgt x * f (m, j x) ∂measure)).mpr
  simpa only [smul_eq_mul] using
    CompactManifoldVectorIntegral.contMDiff_weightedIntegral measure wgt j hf

/-- The smooth slice at a fixed parameter of a jointly smooth family. -/
def plotSmoothFamilySlice :
    let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    let := smoothChartedSpace F M hsmooth
    ∀ (f : M∞ × N → ℂ), ContMDiff ((IM).prod 𝓘(ℝ, H)) Iℂ ∞ f → N → S := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F M hsmooth
  dsimp only
  intro f hf n
  exact ⟨fun m => f (m, n), (isPlotSmooth_iff_contMDiff F M hsmooth _).mpr
    (hf.comp (contMDiff_id.prodMk contMDiff_const))⟩

/-- Every actual enveloping derivative of a compact weighted integral is the weighted
integral of the corresponding slice derivatives. -/
theorem compactIntegralPlotSmooth_enveloping :
    let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    let := smoothChartedSpace F M hsmooth
    ∀ (f : M∞ × N → ℂ) (hf : ContMDiff ((IM).prod 𝓘(ℝ, H)) Iℂ ∞ f) (a : U) (m : M∞),
      (D a (compactIntegralPlotSmooth (H := H) hsmooth measure wgt j f hf)).val m =
        ∫ x, wgt x * (D a (plotSmoothFamilySlice (H := H) hsmooth f hf (j x))).val m ∂measure := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F M hsmooth
  let := smoothLieGroup F M hsmooth
  let : IsManifold IM ∞ M∞ := smoothIsManifold F M hsmooth
  let : LieGroup IM (minSmoothness ℝ 3) M∞ := LieGroup.of_le (n := ∞) (by simp)
  dsimp only
  intro f hf a
  let R := compactIntegralPlotSmooth (H := H) hsmooth measure wgt j
  let T : U → Prop := fun a => ∃ (g : M∞ × N → ℂ) (hg : ContMDiff ((IM).prod 𝓘(ℝ, H)) Iℂ ∞ g),
    (∀ n, plotSmoothFamilySlice (H := H) hsmooth g hg n = D a (plotSmoothFamilySlice (H := H) hsmooth f hf n)) ∧
      R g hg = D a (R f hf)
  have hintegrable {g : M∞ × N → ℂ} (hg : ContMDiff ((IM).prod 𝓘(ℝ, H)) Iℂ ∞ g) (m : M∞) :
      Integrable (fun x => wgt x * g (m, j x)) measure :=
    (wgt.continuous.mul (hg.continuous.comp (continuous_const.prodMk j.continuous)))
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have ha : T a := by
    induction a using complexEnveloping_real_left_induction with
    | h1 => exact ⟨f, hf, fun _ => by rw [map_one, Module.End.one_apply],
        by simp only [map_one, Module.End.one_apply]⟩
    | hadd a b ha hb =>
      obtain ⟨g, hg, hgs, hgi⟩ := ha
      obtain ⟨k, hk, hks, hki⟩ := hb
      refine ⟨g + k, hg.add hk, ?_, ?_⟩
      · intro n
        rw [map_add, LinearMap.add_apply, ← hgs, ← hks]
        rfl
      · rw [map_add, LinearMap.add_apply, ← hgi, ← hki]
        apply Subtype.ext
        funext m
        change (∫ x, wgt x * (g (m, j x) + k (m, j x)) ∂measure) = _
        simp only [mul_add]
        exact integral_add (hintegrable hg m) (hintegrable hk m)
    | hsmul c a ha =>
      obtain ⟨g, hg, hgs, hgi⟩ := ha
      have hcg : ContMDiff ((IM).prod 𝓘(ℝ, H)) Iℂ ∞ (c • g) :=
        ((ContinuousLinearMap.mul ℝ ℂ c).contDiff.contMDiff).comp hg
      refine ⟨c • g, hcg, ?_, ?_⟩
      · intro n
        rw [map_smul, LinearMap.smul_apply, ← hgs]
        rfl
      · rw [map_smul, LinearMap.smul_apply, ← hgi]
        apply Subtype.ext
        funext m
        change (∫ x, wgt x * (c * g (m, j x)) ∂measure) = c * ∫ x, wgt x * g (m, j x) ∂measure
        simp_rw [mul_left_comm (wgt _) c, integral_const_mul]
    | hgen Y a ha =>
      obtain ⟨g, hg, hgs, hgi⟩ := ha
      let dg (p : M∞ × N) := groupDirectionalValue IM Y (fun m => g (m, p.2)) p.1
      have hdg := contMDiff_firstGroupDirectionalValue (V := smoothModel F d) Y hg
      refine ⟨dg, hdg, ?_, ?_⟩
      · intro n
        rw [map_mul, Module.End.mul_apply, ← hgs, plotSmoothEnvelopingAction_real_generator]
        rfl
      · rw [map_mul, Module.End.mul_apply, ← hgi, plotSmoothEnvelopingAction_real_generator]
        apply Subtype.ext
        funext m
        let gp (p : M∞ × N) := g (m * p.1, p.2)
        have hgp : ContMDiff ((IM).prod 𝓘(ℝ, H)) Iℂ ∞ gp :=
          hg.comp ((contMDiff_const.mul contMDiff_fst).prodMk contMDiff_snd)
        exact (CompactManifoldVectorIntegral.mfderiv_weightedIntegral_apply measure wgt j hgp 1 Y).symm
  obtain ⟨g, hg, hgs, hgi⟩ := ha
  intro m
  rw [← hgi]
  change (∫ x, wgt x * (plotSmoothFamilySlice (H := H) hsmooth g hg (j x)).val m ∂measure) = _
  simp only [hgs]

end Langlands.Global.InfiniteAdelicGroupPoints
