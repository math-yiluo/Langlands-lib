import Langlands.Automorphic.GeneralLinearOperatorEvaluation
import Langlands.Automorphic.GroupSchemeInvariantFormsComparison
import Langlands.Global.EisensteinMeromorphicDetection

/-! # Continuing the operator tests of a finite Eisenstein family -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Set Filter
open scoped CategoryTheory.MonObj Manifold Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1250000

namespace Langlands.Global.EisensteinJet

open Langlands.Analysis.Meromorphic
open Langlands.Automorphic Langlands.Automorphic.GroupSchemeFunctions UniformGrowthFrechetSpace

private theorem eqOn_of_local_scalar_normalizations {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (g : E → ℂ)
    (hlocal : ∀ z : E, ∃ r > 0, ∃ (V : Set E) (a h : E → ℂ),
      IsOpen V ∧ V ⊆ Metric.ball z r ∧ Metric.ball z r ⊆ closure V ∧
      DifferentiableOn ℂ a (Metric.ball z r) ∧ DifferentiableOn ℂ h (Metric.ball z r) ∧
      ∀ t ∈ V, a t ≠ 0 ∧ h t = a t * g t)
    {C O : Set E} (hC : IsOpen C) (hne : C.Nonempty) (hzero : ∀ t ∈ C, g t = 0)
    (hO : IsOpen O) (hd : DifferentiableOn ℂ g O) : ∀ t ∈ O, g t = 0 := by
  let lift (v : ℂ) : ℂ →ₗ[ℂ] (Unit → ℂ) := LinearMap.toSpanSingleton ℂ (Unit → ℂ) (fun _ => v)
  let family (t : E) := lift (g t)
  have hloc : HasLocalHolomorphicNumerators univ family := by
    intro z _
    obtain ⟨r, hr, V, a, h, hV, hsub, hcl, ha, hh, heq⟩ := hlocal z
    refine ⟨Metric.ball z r, V, a, fun t => lift (h t), Metric.isOpen_ball,
      (convex_ball z r).isPreconnected, Metric.mem_ball_self hr, subset_univ _, hV, hsub, hcl,
      ha, fun c _ => ?_, ?_⟩
    · exact (differentiableOn_const (c := c)).mul hh
    · intro t ht
      refine ⟨(heq t ht).1, LinearMap.ext fun c => ?_⟩
      funext p
      change c * h t = a t * (c * g t)
      rw [(heq t ht).2, mul_left_comm]
  intro t ht
  by_contra htne
  have htreg : t ∈ regularParameterSet univ family :=
    ⟨O, hO, ht, subset_univ _, fun c _ => (differentiableOn_const (c := c)).mul hd⟩
  have hinj : Function.Injective (family t) := fun c b hcb =>
    mul_right_cancel₀ htne (congrFun hcb ())
  obtain ⟨s, hs, hsi⟩ := hloc.exists_injective_of_open isOpen_univ isPreconnected_univ
    (mem_univ t) htreg hinj hC (subset_univ _) hne
  have hz : family s 1 = family s 0 := by
    funext p
    change 1 * g s = 0 * g s
    rw [hzero s hs.1, mul_zero, mul_zero]
  exact one_ne_zero (hsi hz)

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

local notation "GL[" F "," n "]" =>
  Langlands.GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)

local instance eisensteinOperatorContinuationAffine :
    IsAffine (GL[F, n] : GroupScheme (Spec (CommRingCat.of F))).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

local notation "Adeles" => AdelicGroupPoints F GL[F, n]

local instance eisensteinOperatorContinuationAddCommGroup :
    AddCommGroup (FinitePlotSmoothRationalFunctions F GL[F, n]) :=
  Module.addCommMonoidToAddCommGroup ℂ

private def matrixEvaluation : Langlands.Automorphic.FiniteSmoothRationalFunctions F n →ₗ[ℂ]
    (Adeles → ℂ) where
  toFun f x := ContinuousRationalFunctions.evaluate F n f.val
    (GeneralLinearGroupPoints.adelicHomeomorph F n x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A linear extension of a concrete operator to scalar functions. On the actual
finite-smooth rational-invariant functions it is the original matrix action. -/
def scalarAutomorphicOperator (a : automorphicOperatorAlgebra F n) :
    (Adeles → ℂ) →ₗ[ℂ] (Adeles → ℂ) :=
  (matrixEvaluation F n).comp (a.val.comp ((finitePlotSmoothGeneralLinearEquiv F n).toLinearMap.comp
    (finitePlotSmoothEvaluation F GL[F, n]).leftInverse))

theorem scalarAutomorphicOperator_evaluate (a : automorphicOperatorAlgebra F n)
    (v : FinitePlotSmoothRationalFunctions F GL[F, n]) (x : Adeles) :
    scalarAutomorphicOperator F n a (finitePlotSmoothEvaluation F GL[F, n] v) x =
      ContinuousRationalFunctions.evaluate F n (a.val (finitePlotSmoothGeneralLinearEquiv F n v)).val
        (GeneralLinearGroupPoints.adelicHomeomorph F n x) := by
  simp only [scalarAutomorphicOperator, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr
    (finitePlotSmoothEvaluation_injective F GL[F, n]))]
  rfl

variable {N d : ℕ} (rho : Langlands.GroupScheme.MatrixRepresentation GL[F, n] (Fin N))
  (hsmooth : SmoothOfRelativeDimension d (GL[F, n] : GroupScheme (Spec (CommRingCat.of F))).X.hom)
  (hcalc : AdelicDifferentialCommutator F GL[F, n] hsmooth)
  (hN : 0 < N) (hrho : Langlands.GroupScheme.IsClosedSubgroup rho)

local notation "Growth[" R "," L "]" => UniformGrowthFrechetSpace F GL[F, n] rho hsmooth hcalc hN hrho R L
local notation "value[" R "," L "]" => UniformGrowthFrechetSpace.toFun F GL[F, n] rho hsmooth hcalc hN hrho R L
local notation "test[" R "," L "]" => generalLinearOperatorEvaluation F n rho hsmooth hcalc hN hrho R L

/-- On growth vectors the scalar extension gives exactly the continuous operator test. -/
theorem scalarAutomorphicOperator_toFun (R : ℝ) (L : Subgroup (FiniteAdelicGroupPoints F GL[F, n]))
    (a : automorphicOperatorAlgebra F n) (v : Growth[R, L]) (x : Adeles) :
    scalarAutomorphicOperator F n a (value[R, L] v) x = test[R, L] a x v := by
  rw [generalLinearOperatorEvaluation_apply]
  exact scalarAutomorphicOperator_evaluate F n a
    (v : uniformGrowthLevelSubmodule F GL[F, n] rho hsmooth hcalc R L).val x

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {m : ℕ}

private theorem differentiableOn_varyingCombination (c : E → Fin m → ℂ) {W : Set E}
    (hc : ∀ j, DifferentiableOn ℂ (fun t => c t j) W)
    {Y : Type*} [AddCommMonoid Y] [Module ℂ Y]
    (J : E → (Fin m → ℂ) →ₗ[ℂ] Y) (l : Y →ₗ[ℂ] ℂ)
    (hJ : ∀ v, DifferentiableOn ℂ (fun t => l (J t v)) W) :
    DifferentiableOn ℂ (fun t => l (J t (c t))) W := by
  have hsingle (i : Fin m) : (fun j => if i = j then (1 : ℂ) else 0) = Pi.single i 1 := by
    funext j
    by_cases h : i = j
    · subst j
      simp
    · simp [h]
  have heq : (fun t => l (J t (c t))) = fun t =>
      ∑ j, c t j * l (J t (Pi.single j 1)) := by
    funext t
    simpa only [LinearMap.comp_apply, smul_eq_mul, hsingle] using
      ((l.comp (J t)).pi_apply_eq_sum_univ (c t))
  rw [heq]
  apply DifferentiableOn.fun_sum
  exact fun j _ => (hc j).mul (hJ (Pi.single j 1))

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
private theorem normalized_operatorCombination_on_regular (a : Fin m → automorphicOperatorAlgebra F n)
    (f : Fin m → E → Adeles → ℂ) (x : Adeles) (t : E) (b : ℂ)
    (R : ℝ) (L : Subgroup (FiniteAdelicGroupPoints F GL[F, n]))
    (J : (Fin m → ℂ) →ₗ[ℂ] Growth[R, L])
    (hEq : ∀ c, value[R, L] (J c) = b • continuedLinearCombination f t c) :
    (∑ j, test[R, L] (a j) x (J (Pi.single j 1))) =
      b * ∑ j, scalarAutomorphicOperator F n (a j) (f j t) x := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hb : continuedLinearCombination f t (Pi.single j 1) = f j t := by
    rw [continuedLinearCombination_apply, Finset.sum_eq_single j]
    · simp
    · intro i _ hi
      rw [Pi.single_eq_of_ne hi, zero_smul]
    · simp
  rw [← scalarAutomorphicOperator_toFun, hEq, hb, map_smul, Pi.smul_apply, smul_eq_mul]

/-- An evaluated operator identity for a varying finite section combination, known
on an open anchor, holds after normalization throughout the specialization ball. -/
theorem normalized_operatorCombination_eqOn_of_anchor
    (a : Fin m → automorphicOperatorAlgebra F n) (f : Fin m → E → Adeles → ℂ)
    (hlocal : ∀ j z, ∃ B : TopologicalSpace.Opens E, z ∈ B ∧
      ∃ (R : ℝ) (L : Subgroup (FiniteAdelicGroupPoints F GL[F, n])),
        IsOpen (L : Set (FiniteAdelicGroupPoints F GL[F, n])) ∧
        ∃ (v : B → Growth[R, L]) (D : Set B), IsMeromorphicOn 𝓘(ℂ, E) v D ∧
          ∀ t ∈ D, value[R, L] (v t) = f j t.val)
    (c : E → Fin m → ℂ) (hc : ∀ j, Differentiable ℂ (fun t => c t j))
    {C : Set E} (hC : IsOpen C) (hne : C.Nonempty)
    (hanchor : ∀ t ∈ C, ∀ x,
      (∑ j, scalarAutomorphicOperator F n (a j) (f j t) x) = continuedLinearCombination f t (c t) x)
    {z : E} {r : ℝ} (hr : 0 < r) (R : ℝ) (L : Subgroup (FiniteAdelicGroupPoints F GL[F, n]))
    (J : E → (Fin m → ℂ) →ₗ[ℂ] Growth[R, L]) (b : E → ℂ)
    (hb : DifferentiableOn ℂ b (Metric.ball z r))
    (hJ : ∀ v (l : Growth[R, L] →L[ℂ] ℂ), DifferentiableOn ℂ (fun t => l (J t v)) (Metric.ball z r))
    {V : Set E} (hV : IsOpen V) (hsub : V ⊆ Metric.ball z r) (hcl : Metric.ball z r ⊆ closure V)
    (hEq : ∀ t ∈ V, b t ≠ 0 ∧ ∀ v, value[R, L] (J t v) = b t • continuedLinearCombination f t v)
    (x : Adeles) :
    EqOn (fun t => ∑ j, test[R, L] (a j) x (J t (Pi.single j 1)))
      (fun t => value[R, L] (J t (c t)) x) (Metric.ball z r) := by
  classical
  let g (t : E) := (∑ j, scalarAutomorphicOperator F n (a j) (f j t) x) -
    continuedLinearCombination f t (c t) x
  let numerator (S : ℝ) (M : Subgroup (FiniteAdelicGroupPoints F GL[F, n]))
      (H : E → (Fin m → ℂ) →ₗ[ℂ] Growth[S, M]) (t : E) :=
    (∑ j, test[S, M] (a j) x (H t (Pi.single j 1))) - value[S, M] (H t (c t)) x
  have hdiff (S : ℝ) (M : Subgroup (FiniteAdelicGroupPoints F GL[F, n]))
      (H : E → (Fin m → ℂ) →ₗ[ℂ] Growth[S, M]) {W : Set E}
      (hH : ∀ v (l : Growth[S, M] →L[ℂ] ℂ), DifferentiableOn ℂ (fun t => l (H t v)) W) :
      DifferentiableOn ℂ (numerator S M H) W := by
    have hsum : DifferentiableOn ℂ (fun t => ∑ j, test[S, M] (a j) x (H t (Pi.single j 1))) W :=
      DifferentiableOn.fun_sum fun j _ => hH _ (test[S, M] (a j) x)
    let ev := UniformGrowthFrechetSpace.evaluation F GL[F, n] rho hsmooth hcalc hN hrho S M x
    exact hsum.sub (differentiableOn_varyingCombination c (fun j => (hc j).differentiableOn)
      H ev.toLinearMap (fun v => hH v ev))
  have hnorm (S : ℝ) (M : Subgroup (FiniteAdelicGroupPoints F GL[F, n]))
      (H : E → (Fin m → ℂ) →ₗ[ℂ] Growth[S, M]) (t : E) (b : ℂ)
      (h : ∀ v, value[S, M] (H t v) = b • continuedLinearCombination f t v) :
      numerator S M H t = b * g t := by
    dsimp only [numerator, g]
    rw [normalized_operatorCombination_on_regular F n rho hsmooth hcalc hN hrho a f x t b S M
      (H t) h, h, Pi.smul_apply, smul_eq_mul, mul_sub]
  have hnorms : ∀ y : E, ∃ s > 0, ∃ (O : Set E) (A H : E → ℂ),
      IsOpen O ∧ O ⊆ Metric.ball y s ∧ Metric.ball y s ⊆ closure O ∧
      DifferentiableOn ℂ A (Metric.ball y s) ∧ DifferentiableOn ℂ H (Metric.ball y s) ∧
      ∀ t ∈ O, A t ≠ 0 ∧ H t = A t * g t := by
    intro y
    choose B hy R L hL v D hv hf using fun j => hlocal j y
    obtain ⟨s, hs, S, M, _hM, A, H, O, hA, hH, hO, hOb, hOcl, hOeq⟩ :=
      exists_common_normalization_of_meromorphic F GL[F, n] rho hsmooth hcalc hN hrho
        y B hy R L hL v D hv f hf
    exact ⟨s, hs, O, A, numerator S M H, hO, hOb, hOcl, hA, hdiff S M H hH,
      fun t ht => ⟨(hOeq t ht).2.1, hnorm S M H t (A t) (hOeq t ht).2.2⟩⟩
  have hgrepr : EqOn g (fun t => numerator R L J t / b t) V := by
    intro t ht
    change g t = numerator R L J t / b t
    rw [hnorm R L J t (b t) (hEq t ht).2, mul_div_cancel_left₀ _ (hEq t ht).1]
  have hquot : DifferentiableOn ℂ (fun t => numerator R L J t / b t) V := by
    simp_rw [div_eq_mul_inv]
    change DifferentiableOn ℂ (numerator R L J * b⁻¹) V
    exact ((hdiff R L J hJ).mono hsub).mul ((hb.mono hsub).inv fun t ht => (hEq t ht).1)
  have hgd : DifferentiableOn ℂ g V := hquot.congr hgrepr
  have hgz := eqOn_of_local_scalar_normalizations g hnorms hC hne
    (fun t ht => sub_eq_zero.mpr (hanchor t ht x)) hV hgd
  obtain ⟨t₀, ht₀⟩ := closure_nonempty_iff.mp ⟨z, hcl (Metric.mem_ball_self hr)⟩
  have hz0 : numerator R L J =ᶠ[𝓝 t₀] 0 :=
    Filter.eventually_of_mem (hV.mem_nhds ht₀) fun t ht => by
      rw [hnorm R L J t (b t) (hEq t ht).2, hgz t ht, mul_zero, Pi.zero_apply]
  have hzero := eqOn_zero_of_differentiableOn_of_eventuallyEq_zero Metric.isOpen_ball
    (convex_ball z r).isPreconnected (hdiff R L J hJ) (hsub ht₀) hz0
  intro t ht
  exact sub_eq_zero.mp (hzero t ht)

end Langlands.Global.EisensteinJet
