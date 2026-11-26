import Langlands.Automorphic.GroupSchemeInvariantFunctionGrowth
import Langlands.Automorphic.GroupSchemeCompactDifferentialPolynomial
import Langlands.Automorphic.GroupSchemeAdaptedCasimirProof
import Langlands.Geometry.Manifold.LieGroupEllipticEstimateProof
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.TensorProduct.Finite

/-! # Common elliptic estimates for a fixed compact profile space and center ideal -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Manifold ContDiff TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global InfiniteAdelicGroupPoints Langlands.GroupScheme
  Langlands.Geometry.Manifold UniformGrowthReduction

private theorem commonPolynomial_add {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T U : Module.End ℂ V) (hcomm : Commute T U) (p q : Polynomial ℂ)
    (hp : p.Monic) (hq : q.Monic) :
    ∃ r : Polynomial ℂ, r.Monic ∧ ∀ f : V, Polynomial.aeval T p f = 0 →
      Polynomial.aeval U q f = 0 → Polynomial.aeval (T + U) r f = 0 := by
  let S := LinearMap.ker (Polynomial.aeval T p) ⊓ LinearMap.ker (Polynomial.aeval U q)
  have hmem {x : V} : x ∈ S ↔ Polynomial.aeval T p x = 0 ∧ Polynomial.aeval U q x = 0 := by
    simp only [S, Submodule.mem_inf, LinearMap.mem_ker]
  have hstable (A : Module.End ℂ V) (hAT : Commute A T) (hAU : Commute A U) (f : V) (hf : f ∈ S) :
      A f ∈ S := by
    obtain ⟨hf₁, hf₂⟩ := hmem.mp hf
    have h (B : Module.End ℂ V) (hAB : Commute A B) (w : Polynomial ℂ)
        (hfB : Polynomial.aeval B w f = 0) : Polynomial.aeval B w (A f) = 0 := by
      have hm := endomorphism_aeval_intertwine A B B
        (fun x => congrArg (fun D : Module.End ℂ V => D x) hAB.eq) w f
      rw [hfB, map_zero] at hm
      exact hm.symm
    exact hmem.mpr ⟨h T hAT p hf₁, h U hAU q hf₂⟩
  let Tₛ := T.restrict (hstable T (Commute.refl _) hcomm)
  let Uₛ := U.restrict (hstable U hcomm.symm (Commute.refl _))
  have hTU : Commute Tₛ Uₛ := by
    apply LinearMap.ext
    intro v
    exact Subtype.ext (congrArg (fun D : Module.End ℂ V => D v.val) hcomm.eq)
  have ht : IsIntegral ℂ Tₛ := by
    refine ⟨p, hp, ?_⟩
    change Polynomial.aeval Tₛ p = 0
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change ((Polynomial.aeval Tₛ p v : S) : V) = 0
    rw [restrict_aeval_apply]
    exact (hmem.mp v.property).1
  have hu : IsIntegral ℂ Uₛ := by
    refine ⟨q, hq, ?_⟩
    change Polynomial.aeval Uₛ q = 0
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change ((Polynomial.aeval Uₛ q v : S) : V) = 0
    rw [restrict_aeval_apply]
    exact (hmem.mp v.property).2
  let A := Algebra.adjoin ℂ ({Tₛ} : Set (Module.End ℂ S))
  let B := Algebra.adjoin ℂ ({Uₛ} : Set (Module.End ℂ S))
  let : Ring A := (Algebra.adjoin ℂ ({Tₛ} : Set (Module.End ℂ S))).toRing
  let : Ring (A ⊗[ℂ] B) := Algebra.TensorProduct.instRing
  let : Module.Finite ℂ A := Algebra.finite_adjoin_simple_of_isIntegral ht
  let : Module.Finite ℂ B := Algebra.finite_adjoin_simple_of_isIntegral hu
  have hAB (x : A) (y : B) : Commute (A.val x) (B.val y) :=
    Algebra.commute_of_mem_adjoin_singleton_of_commute y.property
      (Algebra.commute_of_mem_adjoin_singleton_of_commute x.property hTU.symm).symm
  let φ : A ⊗[ℂ] B →ₐ[ℂ] Module.End ℂ S := Algebra.TensorProduct.lift A.val B.val hAB
  let t : A := ⟨Tₛ, Algebra.subset_adjoin (Set.mem_singleton _)⟩
  let u : B := ⟨Uₛ, Algebra.subset_adjoin (Set.mem_singleton _)⟩
  let a : A ⊗[ℂ] B := t ⊗ₜ[ℂ] 1 + 1 ⊗ₜ[ℂ] u
  have ha : φ a = Tₛ + Uₛ := by
    have hl : φ (t ⊗ₜ[ℂ] 1) = Tₛ := by
      simp only [φ, Algebra.TensorProduct.lift_tmul, map_one, mul_one]
      rfl
    have hr : φ (1 ⊗ₜ[ℂ] u) = Uₛ := by
      simp only [φ, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
      rfl
    exact (φ.toLinearMap.map_add (t ⊗ₜ[ℂ] 1) (1 ⊗ₜ[ℂ] u)).trans (congrArg₂ (· + ·) hl hr)
  have hi : IsIntegral ℂ (Tₛ + Uₛ) := ha ▸ (IsIntegral.of_finite ℂ a).map φ
  obtain ⟨r, hr, hAnnₛ⟩ := hi
  change Polynomial.aeval (Tₛ + Uₛ) r = 0 at hAnnₛ
  refine ⟨r, hr, fun f hf hg => ?_⟩
  let fₛ : S := ⟨f, hmem.mpr ⟨hf, hg⟩⟩
  have h := endomorphism_aeval_intertwine S.subtype (Tₛ + Uₛ) (T + U) (fun _ => rfl) r fₛ
  rw [hAnnₛ, LinearMap.zero_apply, map_zero] at h
  exact h.symm

private theorem monic_evaluation_mem_cofinite_ideal {A : Type*} [CommRing A] [Algebra ℂ A]
    (J : Ideal A) (hJ : Module.Finite ℂ (A ⧸ J.restrictScalars ℂ)) (z : A) :
    ∃ p : Polynomial ℂ, p.Monic ∧ Polynomial.aeval z p ∈ J := by
  let : Module.Finite ℂ (A ⧸ J) := hJ
  let π := Ideal.Quotient.mkₐ ℂ J
  obtain ⟨p, hp, hp0⟩ := Algebra.IsIntegral.isIntegral (R := ℂ) (π z)
  refine ⟨p, hp, (Ideal.Quotient.eq_zero_iff_mem).mp ?_⟩
  change π (Polynomial.aeval z p) = 0
  rw [← Polynomial.aeval_algHom_apply]
  exact hp0

section PlotSmoothWords

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left] {d : ℕ}
  (hsmooth : SmoothOfRelativeDimension d G.X.hom) (hcalc : AdelicDifferentialCommutator F G hsmooth)

local notation "V" => InfinitePlotSmoothFunctions F G
local notation "M" => InfiniteAdelicGroupPoints F G
local notation "U" => AdelicEnvelopingAlgebra F G hsmooth
local notation "Act" => plotSmoothEnvelopingAction F G hsmooth hcalc

end PlotSmoothWords

/-- Every differential of a smooth function with prescribed compact profiles and center ideal
is bounded, at any point, by a fixed local supremum of that function. -/
def FixedProfileInteriorEstimateStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth),
    IsConnectedReductive G → ∀ (H : Subgroup (InfiniteAdelicGroupPoints F G)),
      CompactIwasawa.IsMaximalCompact H → ∀ (J : Ideal (AdelicEnvelopingCenter F G hsmooth)),
      Module.Finite ℂ (AdelicEnvelopingCenter F G hsmooth ⧸ J.restrictScalars ℂ) →
    ∀ (E : Submodule ℂ (H → ℂ)), FiniteDimensional ℂ E →
    ∀ D : AdelicEnvelopingAlgebra F G hsmooth,
      ∃ (K : Set (InfiniteAdelicGroupPoints F G)) (C : ℝ), IsCompact K ∧ 0 ≤ C ∧
        ∀ f : InfinitePlotSmoothFunctions F G,
          (∀ z ∈ J, plotSmoothCenterAction F G hsmooth hcalc z f = 0) →
          (∀ a, rightCompactProfile H a f.val ∈ E) →
          ∀ (g : InfiniteAdelicGroupPoints F G) (B : ℝ), (∀ k ∈ K, ‖f.val (g * k)‖ ≤ B) →
            ‖(plotSmoothEnvelopingAction F G hsmooth hcalc D f).val g‖ ≤ C * B

set_option maxHeartbeats 650000 in
/-- Fixed profiles and a common cofinite center ideal give a common elliptic equation. -/
theorem fixedProfileInteriorEstimate : FixedProfileInteriorEstimateStatement.{u} := by
  classical
  intro F _ _ G _ d hsmooth hcalc hG H hH J hJ E hE D
  let act := plotSmoothEnvelopingAction F G hsmooth hcalc
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3) (InfiniteAdelicGroupPoints F G) :=
    LieGroup.of_le (n := ∞) (by simp)
  obtain ⟨n, X, I, hspan, hcurve, hcent⟩ := adelicAdaptedCasimir F G H hsmooth hG hH
  let iX (i : Fin n) : AdelicEnvelopingAlgebra F G hsmooth :=
    UniversalEnvelopingAlgebra.ι ℂ
      (L := ℂ ⊗[ℝ] GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G))
      ((1 : ℂ) ⊗ₜ[ℝ] X i)
  let Uc : AdelicEnvelopingAlgebra F G hsmooth := (2 : ℂ) • ∑ j ∈ I, iX j ^ 2
  let Us : AdelicEnvelopingAlgebra F G hsmooth := ∑ i, iX i ^ 2
  let z : AdelicEnvelopingCenter F G hsmooth := ⟨Us - Uc, hcent⟩
  have hsum : act Us = act z.val + act Uc := by
    rw [← map_add]
    change act Us = act (Us - Uc + Uc)
    rw [sub_add_cancel]
  have hcomm : Commute (act z.val) (act Uc) :=
    (Commute.symm (Subalgebra.mem_center_iff.mp z.property Uc : Commute _ _)).map act
  have hActc : act Uc = (2 : ℂ) • ∑ j ∈ I, plotSmoothDifferential F G hsmooth (X j) ^ 2 := by
    simp only [act, Uc, iX, map_smul, map_sum, map_pow, plotSmoothEnvelopingAction_real_generator]
  obtain ⟨p, hp, hpAnn⟩ := monic_evaluation_mem_cofinite_ideal J hJ z
  obtain ⟨q, hq, hqAnn⟩ := exists_monic_aeval_compactSquares F G hsmooth H X I E hcurve
  obtain ⟨r, hr, hAnn⟩ := commonPolynomial_add (act z.val) (act Uc) hcomm p q hp hq
  have hkill (f : InfinitePlotSmoothFunctions F G)
      (hf : ∀ z ∈ J, plotSmoothCenterAction F G hsmooth hcalc z f = 0)
      (hprof : ∀ a, rightCompactProfile H a f.val ∈ E) : Polynomial.aeval (act Us) r f = 0 := by
    rw [hsum]
    apply hAnn
    · have hp₀ := hf (Polynomial.aeval z p) hpAnn
      change ((act.comp (Subalgebra.center ℂ (AdelicEnvelopingAlgebra F G hsmooth)).val)
        (Polynomial.aeval z p)) f = 0 at hp₀
      rw [← Polynomial.aeval_algHom_apply] at hp₀
      exact hp₀
    · rw [hActc]
      exact hqAnn f hprof
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
  obtain ⟨Q, rfl⟩ := wordHom_surjective F G hsmooth X hspan D
  obtain ⟨K, C, hK, hC, hest⟩ := lieGroupEllipticInteriorEstimate (smoothModel F d)
    (InfiniteAdelicGroupPoints F G) n (2 * m) X Ptop Plow htop hlow hsym Q
  refine ⟨K, C, hK, hC, fun f hf hprof g B hbound => ?_⟩
  let φ : InfiniteAdelicGroupPoints F G → ℂ := fun y => f.val (g * y)
  have hφ : ContMDiff 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, ℂ) ∞ φ :=
    ((isPlotSmooth_iff_contMDiff F G hsmooth _).mp f.property).comp (contMDiff_const.mul contMDiff_id)
  have heqn : ∀ x, lieWordAction X (Ptop + Plow) φ x = 0 := by
    intro x
    rw [lieWordAction_leftTranslation, ← plotSmoothEnvelopingAction_wordHom F G hsmooth hcalc, hPsum,
      ← Polynomial.aeval_algHom_apply, hΨsq, ← Polynomial.aeval_algHom_apply, hkill f hf hprof]
    rfl
  have h := hest φ hφ heqn B hbound
  rw [lieWordAction_leftTranslation, ← plotSmoothEnvelopingAction_wordHom F G hsmooth hcalc, mul_one] at h
  exact h

end Langlands.Automorphic.GroupSchemeFunctions
