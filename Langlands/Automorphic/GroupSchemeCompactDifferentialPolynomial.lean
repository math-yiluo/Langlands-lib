import Langlands.Automorphic.CompactProfileHull
import Langlands.Automorphic.GroupSchemeAutomorphicUniformGrowthReductionProof
import Mathlib.Algebra.Module.Projective

/-! # A common differential polynomial from fixed compact profiles -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Manifold ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global InfiniteAdelicGroupPoints Langlands.Geometry.Manifold UniformGrowthReduction

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left] {d : ℕ}
  (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (H : Subgroup (InfiniteAdelicGroupPoints F G))

local notation "V" => InfinitePlotSmoothFunctions F G
local notation "M" => InfiniteAdelicGroupPoints F G

private theorem hasDerivAt_plotSmooth_compactCurve
    (X : smoothModel F d) (c : ℝ → M) (hc0 : c 0 = 1) :
    letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    ∀ (_hc : ContMDiff 𝓘(ℝ) 𝓘(ℝ, smoothModel F d) ∞ c)
      (_hcX : mfderiv 𝓘(ℝ) 𝓘(ℝ, smoothModel F d) c 0 1 = X)
      (f : V) (a : M),
      HasDerivAt (fun t => f.val (a * c t)) ((plotSmoothDifferential F G hsmooth X f).val a) 0 := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  intro hc hcX f a
  let g : M → ℂ := fun y => f.val (a * y)
  have hg : ContMDiff 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, ℂ) ∞ g :=
    ((isPlotSmooth_iff_contMDiff F G hsmooth _).mp f.property).comp (contMDiff_const.mul contMDiff_id)
  have hgc := contMDiff_iff_contDiff.mp (hg.comp hc)
  have h := (hgc.differentiable (by simp) 0).hasFDerivAt.hasDerivAt
  change HasDerivAt (g ∘ c) _ 0
  convert h using 1
  have heq : mvfderiv 𝓘(ℝ) (g ∘ c) 0 = fderiv ℝ (g ∘ c) 0 := mvfderiv_eq_fderiv
  rw [plotSmoothDifferential_apply, ← heq]
  exact ((mvfderiv_comp_apply_of_eq 0 (hg.mdifferentiableAt (by simp))
    (hc.mdifferentiableAt (by simp)) hc0 1).trans (congrArg (mvfderiv _ g 1) hcX)).symm

/-- A linear intertwiner of two endomorphisms intertwines their polynomial evaluations. -/
theorem endomorphism_aeval_intertwine {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Module ℂ A] [Module ℂ B] (e : A →ₗ[ℂ] B) (T : Module.End ℂ A) (U : Module.End ℂ B)
    (h : ∀ x, e (T x) = U (e x)) (p : Polynomial ℂ) (a : A) :
    e (Polynomial.aeval T p a) = Polynomial.aeval U p (e a) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq]
  | monomial k c =>
    simp only [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      map_smul]
    congr 1
    induction k generalizing a with
    | zero => rfl
    | succ k ih => rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]

set_option maxHeartbeats 650000 in
/-- A fixed finite profile space bounds the polynomial of a sum of compact tangent squares,
uniformly over all smooth functions with those profiles. The supplied curves measure the
same actual right-orbit derivatives as the plot-smooth enveloping action. -/
theorem exists_monic_aeval_compactSquares {n : ℕ} (X : Fin n → smoothModel F d) (I : Finset (Fin n))
    (E : Submodule ℂ (H → ℂ)) [FiniteDimensional ℂ E] :
    letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    (∀ j ∈ I, ∃ c : ℝ → M, ContMDiff 𝓘(ℝ) 𝓘(ℝ, smoothModel F d) ∞ c ∧ c 0 = 1 ∧
      (∀ t, c t ∈ H) ∧ mfderiv 𝓘(ℝ) 𝓘(ℝ, smoothModel F d) c 0 1 = X j) →
    ∃ p : Polynomial ℂ, p.Monic ∧ ∀ f : V, (∀ a, rightCompactProfile H a f.val ∈ E) →
      Polynomial.aeval ((2 : ℂ) • ∑ j ∈ I, plotSmoothDifferential F G hsmooth (X j) ^ 2) p f = 0 := by
  classical
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  intro hCurve
  choose c hc h0 hcH hcX using hCurve
  let W := rightCompactProfileHull H E
  let S : Submodule ℂ V := (functionsWithCompactProfiles H W).comap
    (InfinitePlotSmoothFunctions F G).subtype
  let P (a : M) : V →ₗ[ℂ] (H → ℂ) :=
    (rightCompactProfile H a).comp (InfinitePlotSmoothFunctions F G).subtype
  have hS (f : V) : f ∈ S ↔ ∀ a, P a f ∈ W := mem_functionsWithCompactProfiles H W f.val
  let D (j : Fin n) : Module.End ℂ V := plotSmoothDifferential F G hsmooth (X j)
  let curve (j : Fin n) (hj : j ∈ I) (t : ℝ) : H := ⟨c j hj t, hcH j hj t⟩
  have hd (j : Fin n) (hj : j ∈ I) (f : V) (a : M) (k : H) :
      HasDerivAt (fun t => P a f (k * curve j hj t)) (P a (D j f) k) 0 := by
    have h := hasDerivAt_plotSmooth_compactCurve F G hsmooth (X j) (c j hj)
      (h0 j hj) (hc j hj) (hcX j hj) f (a * k.val)
    change HasDerivAt (fun t => f.val (a * (k.val * c j hj t)))
      ((plotSmoothDifferential F G hsmooth (X j) f).val (a * k.val)) 0
    simpa only [mul_assoc] using h
  have hD (j : Fin n) (hj : j ∈ I) (f : V) (hf : f ∈ S) : D j f ∈ S := by
    refine (hS _).mpr fun a => ?_
    exact mem_of_hasDerivAt LinearMap.id Function.injective_id W
      (fun t k => P a f (k * curve j hj t))
      (fun t => rightTranslate_mem_rightCompactProfileHull H E (curve j hj t) ((hS f).mp hf a))
      (P a (D j f)) (hd j hj f a)
  have hDeq (j : Fin n) (hj : j ∈ I) (f g : V) (hfg : P 1 f = P 1 g) :
      P 1 (D j f) = P 1 (D j g) := by
    funext k
    apply (hd j hj f 1 k).unique
    have heq : (fun t => P 1 f (k * curve j hj t)) =
        fun t => P 1 g (k * curve j hj t) := by rw [hfg]
    exact heq ▸ hd j hj g 1 k
  let T : Module.End ℂ V := (2 : ℂ) • ∑ j ∈ I, D j ^ 2
  have hT (f : V) (hf : f ∈ S) : T f ∈ S := by
    simp only [T, LinearMap.smul_apply, LinearMap.sum_apply, pow_two, Module.End.mul_apply]
    exact S.smul_mem _ (S.sum_mem fun j hj => hD j hj _ (hD j hj f hf))
  have hTeq (f g : V) (hfg : P 1 f = P 1 g) : P 1 (T f) = P 1 (T g) := by
    simp only [T, LinearMap.smul_apply, LinearMap.sum_apply, pow_two, Module.End.mul_apply,
      map_smul, map_sum]
    exact congrArg ((2 : ℂ) • ·)
      (Finset.sum_congr rfl fun j hj => hDeq j hj _ _ (hDeq j hj f g hfg))
  let T₀ : Module.End ℂ S := T.restrict hT
  let R : S →ₗ[ℂ] (H → ℂ) := (P 1).comp S.subtype
  let e := R.rangeRestrict
  have he : Function.Surjective e := R.surjective_rangeRestrict
  have hRange : LinearMap.range R ≤ W := by
    rintro _ ⟨f, rfl⟩
    exact (hS _).mp f.property 1
  let : FiniteDimensional ℂ (LinearMap.range R) := Submodule.finiteDimensional_of_le hRange
  obtain ⟨s, hs⟩ := e.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr he)
  let A : Module.End ℂ (LinearMap.range R) := (e.comp T₀).comp s
  have hInter (v : S) : e (T₀ v) = A (e v) := by
    have hv : e (s (e v)) = e v := LinearMap.congr_fun hs (e v)
    have hv' : P 1 v.val = P 1 (s (e v)).val := congrArg Subtype.val hv.symm
    exact Subtype.ext (hTeq v.val (s (e v)).val hv')
  let p := minpoly ℂ A
  refine ⟨p, minpoly.monic (Algebra.IsIntegral.isIntegral A), fun f hf => ?_⟩
  have hfS : f ∈ S := (hS f).mpr fun a => rightCompactProfile_mem_hull H E hf a
  have ann_at_one (v : V) (hv : v ∈ S) : (Polynomial.aeval T p v).val 1 = 0 := by
    let v₀ : S := ⟨v, hv⟩
    have h := endomorphism_aeval_intertwine e T₀ A hInter p v₀
    rw [show Polynomial.aeval A p = 0 from minpoly.aeval ℂ A, LinearMap.zero_apply] at h
    have h' := congrArg (fun w : LinearMap.range R => w.val (1 : H)) h
    change ((Polynomial.aeval T₀ p v₀ : S).val).val (1 * (1 : H).val) = 0 at h'
    rw [one_mul, Subgroup.coe_one, restrict_aeval_apply T S hT] at h'
    exact h'
  apply Subtype.ext
  funext a
  let l := plotSmoothLeftTranslation F G a
  have hleft (v : V) : l (T v) = T (l v) := by
    simp only [T, LinearMap.smul_apply, LinearMap.sum_apply, pow_two, Module.End.mul_apply,
      map_smul, map_sum, D, l, plotSmoothDifferential_leftTranslation]
  have ha : l f ∈ S := (hS _).mpr fun x => by
    have hx := (hS _).mp hfS (a * x)
    change (fun k : H => f.val ((a * x) * k.val)) ∈ W at hx
    change (fun k : H => f.val (a * (x * k.val))) ∈ W
    simpa only [mul_assoc] using hx
  have h := ann_at_one (l f) ha
  rw [← endomorphism_aeval_intertwine l T T hleft p f] at h
  change (Polynomial.aeval T p f).val a = 0
  simpa only [l, plotSmoothLeftTranslation_apply, mul_one] using h

end Langlands.Automorphic.GroupSchemeFunctions
