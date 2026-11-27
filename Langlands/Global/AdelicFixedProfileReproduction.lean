import Langlands.Automorphic.GroupSchemeFixedProfileInteriorEstimate
import Langlands.Global.AdelicReproducingKernelProof
import Langlands.Automorphic.GroupSchemeAutomorphicLeftTranslation

/-! # Common archimedean reproduction for fixed compact profiles and a central character -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Set
open scoped CategoryTheory.MonObj ContDiff ENNReal Manifold NNReal TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions
  Langlands.Geometry.Manifold Langlands.Analysis AdelicGroupPoints InfiniteAdelicGroupPoints
  Langlands.Automorphic.UniformGrowthReduction

section Reproduction

variable (F : Type) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth)

local notation "M" => InfiniteAdelicGroupPoints F G
local notation "V" => InfinitePlotSmoothFunctions F G
local notation "Act" => plotSmoothEnvelopingAction F G hsmooth hcalc
local notation "Z" => AdelicEnvelopingCenter F G hsmooth

/-- For a maximal compact subgroup and fixed finite compact profiles, there is a central
operator whose fixed eigenvalue suffices for a common continuous reproducing kernel. -/
theorem exists_reproducingKernel_of_centerEigenvalue (hG : IsConnectedReductive G)
    (H : Subgroup M) (hH : CompactIwasawa.IsMaximalCompact H)
    (E : Submodule ℂ (H → ℂ)) [FiniteDimensional ℂ E] :
    ∃ z : Z, ∀ c : ℂ, ∃ κ : M → ℂ, Continuous κ ∧ HasCompactSupport κ ∧
      ∀ f : V, plotSmoothCenterAction F G hsmooth hcalc z f = c • f →
        (∀ a, Langlands.Automorphic.rightCompactProfile H a f.val ∈ E) →
        f.val 1 = ∫ x, f.val x * κ x ∂(Measure.haar : Measure M) := by
  classical
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3) M := LieGroup.of_le (n := ∞) (by simp)
  obtain ⟨n, X, I, hspan, hcurve, hcent⟩ := adelicAdaptedCasimir F G H hsmooth hG hH
  let iX (i : Fin n) : AdelicEnvelopingAlgebra F G hsmooth :=
    UniversalEnvelopingAlgebra.ι ℂ
      (L := ℂ ⊗[ℝ] GroupLieAlgebra 𝓘(ℝ, smoothModel F d) M) ((1 : ℂ) ⊗ₜ[ℝ] X i)
  let Uc : AdelicEnvelopingAlgebra F G hsmooth := (2 : ℂ) • ∑ j ∈ I, iX j ^ 2
  let Us : AdelicEnvelopingAlgebra F G hsmooth := ∑ i, iX i ^ 2
  let z : Z := ⟨Us - Uc, hcent⟩
  have hsum : Act Us = Act z.val + Act Uc := by
    rw [← map_add]
    change Act Us = Act (Us - Uc + Uc)
    rw [sub_add_cancel]
  have hcomm : Commute (Act z.val) (Act Uc) :=
    (Commute.symm (Subalgebra.mem_center_iff.mp z.property Uc : Commute _ _)).map Act
  have hActc : Act Uc = (2 : ℂ) • ∑ j ∈ I, plotSmoothDifferential F G hsmooth (X j) ^ 2 := by
    simp only [Uc, iX, map_smul, map_sum, map_pow, plotSmoothEnvelopingAction_real_generator]
  obtain ⟨q, hq, hqAnn⟩ := exists_monic_aeval_compactSquares F G hsmooth H X I E hcurve
  refine ⟨z, fun c => ?_⟩
  let r := Polynomial.X * q.comp (Polynomial.X - Polynomial.C c)
  have hr : r.Monic := Polynomial.monic_X.mul (hq.comp_X_sub_C c)
  have hrpos : 0 < r.natDegree := by
    rw [show r = Polynomial.X * q.comp (Polynomial.X - Polynomial.C c) from rfl,
      Polynomial.natDegree_mul Polynomial.X_ne_zero (hq.comp_X_sub_C c).ne_zero, Polynomial.natDegree_X]
    omega
  have hkill (f : V) (hf : Act z.val f = c • f) (hprof : ∀ a, Langlands.Automorphic.rightCompactProfile H a f.val ∈ E) :
      Polynomial.aeval (Act Us) r f = 0 := by
    have hpow (k : ℕ) : ((Act Us - algebraMap ℂ _ c) ^ k) f = ((Act Uc) ^ k) f := by
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih, hsum]
        have hComm := congrArg (fun D : Module.End ℂ V => D f) (hcomm.pow_right k).eq
        simp only [Module.End.mul_apply, hf, map_smul] at hComm
        simp only [LinearMap.sub_apply, LinearMap.add_apply, Module.algebraMap_end_apply]
        rw [hComm, add_sub_cancel_left]
    have hrq : Polynomial.aeval (Act Us - algebraMap ℂ _ c) q f = Polynomial.aeval (Act Uc) q f := by
      simp only [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply, LinearMap.smul_apply, hpow]
    change Polynomial.aeval (Act Us) (Polynomial.X * q.comp (Polynomial.X - Polynomial.C c)) f = 0
    rw [map_mul, Module.End.mul_apply, Polynomial.aeval_comp, map_sub, Polynomial.aeval_X,
      Polynomial.aeval_C, hrq, hActc, hqAnn f hprof, map_zero]
  let wsq : MonoidAlgebra ℂ (FreeMonoid (Fin n)) :=
    ∑ i, MonoidAlgebra.single (FreeMonoid.of i * FreeMonoid.of i) 1
  have hΨsq : wordHom F G hsmooth X wsq = Us := by
    simp only [wsq, Us, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_one (1 : ℂ), ← MonoidAlgebra.single_mul_single, map_mul, wordHom_of, pow_two]
  have hsqhom : IsHomogeneous wsq 2 := by
    intro w hw
    rw [MonoidAlgebra.coeff_sum] at hw
    obtain ⟨i, _, hwi⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hw)
    rw [MonoidAlgebra.coeff_single] at hwi
    rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hwi), FreeMonoid.length_mul,
      FreeMonoid.length_of]
  let m := r.natDegree
  let Ptop : MonoidAlgebra ℂ (FreeMonoid (Fin n)) := wsq ^ m
  let Plow : MonoidAlgebra ℂ (FreeMonoid (Fin n)) := ∑ k ∈ Finset.range m, r.coeff k • wsq ^ k
  have hPsum : Ptop + Plow = Polynomial.aeval wsq r := by
    rw [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ, hr.coeff_natDegree, one_smul,
      add_comm]
  have htop : ∀ w ∈ Ptop.coeff.support, w.length = 2 * m := hsqhom.pow m
  have hlow : ∀ w ∈ Plow.coeff.support, w.length < 2 * m :=
    isLower_sum _ _ _ fun k hk => ((hsqhom.pow k).smul _).isLower (by
      have := Finset.mem_range.mp hk
      omega)
  have hsym : ∀ ξ : smoothModel F d →ₗ[ℝ] ℝ, ξ ≠ 0 → lieWordSymbol X ξ Ptop ≠ 0 := by
    intro ξ hξ
    have hω : lieWordSymbol X ξ wsq = ((∑ i, ξ (X i) ^ 2 : ℝ) : ℂ) := by
      simp only [wsq, map_sum, lieWordSymbol, MonoidAlgebra.lift_single, one_smul, map_mul,
        FreeMonoid.lift_eval_of]
      push_cast
      simp only [pow_two]
      rfl
    have hex : ∃ i, ξ (X i) ≠ 0 := by
      by_contra hne
      simp only [not_exists, not_not] at hne
      apply hξ
      have hle : Submodule.span ℝ (Set.range X) ≤ LinearMap.ker ξ := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact hne i
      rw [hspan, top_le_iff, LinearMap.ker_eq_top] at hle
      exact hle
    obtain ⟨i, hi⟩ := hex
    have hpos : 0 < ∑ i, ξ (X i) ^ 2 :=
      Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ _, by positivity⟩
    rw [map_pow, hω]
    exact pow_ne_zero _ (by exact_mod_cast hpos.ne')
  let S0 := LinearMap.ker (Polynomial.aeval (Act Us) r)
  let S : Submodule ℂ (M → ℂ) := S0.map (InfinitePlotSmoothFunctions F G).subtype
  have hsolution (f : V) (hf : f ∈ S0) (x : M) : lieWordAction X (Ptop + Plow) f.val x = 0 := by
    rw [← plotSmoothEnvelopingAction_wordHom F G hsmooth hcalc, hPsum,
      ← Polynomial.aeval_algHom_apply, hΨsq, ← Polynomial.aeval_algHom_apply]
    exact congrArg (fun f : V => f.val x) (LinearMap.mem_ker.mp hf)
  have hsmoothS {f : M → ℂ} (hf : f ∈ S) : ContMDiff 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, ℂ) ∞ f := by
    obtain ⟨f, _, rfl⟩ := Submodule.mem_map.mp hf
    exact (isPlotSmooth_iff_contMDiff F G hsmooth _).mp f.property
  have hleft (f : M → ℂ) (hf : f ∈ S) (a : M) : (fun x => f (a * x)) ∈ S := by
    obtain ⟨f, hf0, rfl⟩ := Submodule.mem_map.mp hf
    refine Submodule.mem_map.mpr ⟨plotSmoothLeftTranslation F G a f, LinearMap.mem_ker.mpr ?_, rfl⟩
    have hA : Act (Polynomial.aeval Us r) = Polynomial.aeval (Act Us) r := by
      rw [Polynomial.aeval_algHom_apply]
    have hzero : Act (Polynomial.aeval Us r) f = 0 := by
      rw [hA]
      exact LinearMap.mem_ker.mp hf0
    rw [← hA, plotSmoothEnvelopingAction_leftTranslation hcalc, hzero, map_zero]
  let ν : Measure M := Measure.haar
  have : ν.IsInvInvariant := infiniteHaarInvInvariant_of_connectedReductive F G hG
  obtain ⟨B, C, hB, hC, hest⟩ := exists_lieWord_l2_evaluation ν
    (show 0 < 2 * m from by omega) X Ptop Plow htop hlow hsym
  obtain ⟨κ, hκ, hκc, hrep⟩ := exists_compact_reproducingKernel_of_l2_evaluation ν S
    (fun _ hf => (hsmoothS hf).continuous) hleft B hB C hC (by
      intro f hf
      obtain ⟨f, hsf, rfl⟩ := Submodule.mem_map.mp hf
      exact hest f.val (hsmoothS hf) (hsolution f hsf))
  exact ⟨κ, hκ, hκc, fun f hf hprof => hrep f.val (Submodule.mem_map.mpr
    ⟨f, hkill f hf hprof, rfl⟩)⟩

end Reproduction

end Langlands.Global
