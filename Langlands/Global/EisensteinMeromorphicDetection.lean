import Langlands.Analysis.Meromorphic.ContinuationUniqueness
import Langlands.Analysis.Meromorphic.LocalScalarization
import Langlands.Automorphic.GroupSchemeUniformGrowthEvaluation
import Langlands.Global.EisensteinContinuationNormalization
import Langlands.Global.EisensteinEvaluationMatrix
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Pi

/-! # Propagating injectivity of a finite Eisenstein family -/

noncomputable section

open Set Filter Matrix
open scoped Manifold Topology

set_option autoImplicit false

namespace Langlands.Global.EisensteinJet

open Langlands.Analysis.Meromorphic

variable {E V X : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [AddCommGroup V] [Module ℂ V]

/-- Local numerator data for a linear family with pointwise scalar tests. -/
def HasLocalHolomorphicNumerators (Ω : Set E) (F : E → V →ₗ[ℂ] (X → ℂ)) : Prop :=
  ∀ z ∈ Ω, ∃ (W U : Set E) (a : E → ℂ) (N : E → V →ₗ[ℂ] (X → ℂ)),
    IsOpen W ∧ IsPreconnected W ∧ z ∈ W ∧ W ⊆ Ω ∧
    IsOpen U ∧ U ⊆ W ∧ W ⊆ closure U ∧ DifferentiableOn ℂ a W ∧
    (∀ v x, DifferentiableOn ℂ (fun t => N t v x) W) ∧
    (∀ t ∈ U, a t ≠ 0 ∧ N t = a t • F t)

/-- Parameters with a common local window of scalar holomorphy. -/
def regularParameterSet (Ω : Set E) (F : E → V →ₗ[ℂ] (X → ℂ)) : Set E :=
  {z | ∃ U : Set E, IsOpen U ∧ z ∈ U ∧ U ⊆ Ω ∧
    ∀ v x, DifferentiableOn ℂ (fun t => F t v x) U}

variable {Ω : Set E} {F : E → V →ₗ[ℂ] (X → ℂ)}

theorem isOpen_regularParameterSet : IsOpen (regularParameterSet Ω F) := by
  rw [isOpen_iff_mem_nhds]
  rintro z ⟨U, hU, hz, hUΩ, hd⟩
  exact mem_of_superset (hU.mem_nhds hz) fun t ht => ⟨U, hU, ht, hUΩ, hd⟩

theorem differentiableOn_regularParameterSet (v : V) (x : X) :
    DifferentiableOn ℂ (fun t => F t v x) (regularParameterSet Ω F) := by
  rintro z ⟨U, hU, hz, _, hd⟩
  exact ((hd v x).differentiableAt (hU.mem_nhds hz)).differentiableWithinAt

private theorem subset_regularParameterSet_of_numerator
    {W U : Set E} (hWΩ : W ⊆ Ω) (hU : IsOpen U) (hUW : U ⊆ W)
    {a : E → ℂ} {N : E → V →ₗ[ℂ] (X → ℂ)}
    (ha : DifferentiableOn ℂ a W) (hN : ∀ v x, DifferentiableOn ℂ (fun t => N t v x) W)
    (hEq : ∀ t ∈ U, a t ≠ 0 ∧ N t = a t • F t) :
    U ⊆ regularParameterSet Ω F := by
  intro t ht
  refine ⟨U, hU, ht, hUW.trans hWΩ, fun v x => ?_⟩
  refine (((hN v x).mono hUW).mul ((ha.mono hUW).inv (fun s hs => (hEq s hs).1))).congr ?_
  intro s hs
  simp only [Pi.mul_apply, Pi.inv_apply, (hEq s hs).2, LinearMap.smul_apply, Pi.smul_apply,
    smul_eq_mul, ← div_eq_mul_inv, mul_div_cancel_left₀ _ (hEq s hs).1]

theorem subset_closure_regularParameterSet (hF : HasLocalHolomorphicNumerators Ω F) :
    Ω ⊆ closure (regularParameterSet Ω F) := by
  intro z hz
  obtain ⟨W, U, a, N, _, _, hzW, hWΩ, hU, hUW, hcl, ha, hN, hEq⟩ := hF z hz
  exact closure_mono (subset_regularParameterSet_of_numerator hWΩ hU hUW ha hN hEq) (hcl hzW)

local notation "I" => Fin (Module.finrank ℂ V)

private theorem evaluationMatrix_mulVec_at (p : I → X) (e : V ≃ₗ[ℂ] (I → ℂ))
    (f : V →ₗ[ℂ] (X → ℂ)) (v : V) :
    (evaluationMatrix p e f).mulVec (e v) = fun i => f v (p i) := by
  funext i
  let g : (I → ℂ) →ₗ[ℂ] ℂ := ((LinearMap.proj (p i)).comp f).comp e.symm.toLinearMap
  have h := (g.pi_apply_eq_sum_univ (e v)).symm
  have hsingle (j : I) : (Pi.single j 1 : I → ℂ) = fun k => if j = k then 1 else 0 := by
    funext k
    by_cases h : j = k
    · subst k
      simp
    · simp [h, Ne.symm h]
  simpa only [g, LinearMap.comp_apply, LinearMap.proj_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, evaluationMatrix, mulVec, dotProduct, Matrix.of_apply,
    smul_eq_mul, mul_comm, hsingle] using h

/-- A nonzero evaluation minor certifies an injective member of the family. -/
theorem injective_of_det_evaluationMatrix_ne_zero (p : I → X) (e : V ≃ₗ[ℂ] (I → ℂ))
    (f : V →ₗ[ℂ] (X → ℂ)) (hf : (evaluationMatrix p e f).det ≠ 0) :
    Function.Injective f := by
  intro v w h
  apply e.injective
  apply mulVec_injective_of_det_ne_zero hf
  rw [evaluationMatrix_mulVec_at, evaluationMatrix_mulVec_at, h]

private theorem differentiableOn_det_evaluationMatrix (p : I → X) (e : V ≃ₗ[ℂ] (I → ℂ))
    {F : E → V →ₗ[ℂ] (X → ℂ)} {W : Set E}
    (h : ∀ v x, DifferentiableOn ℂ (fun t => F t v x) W) :
    DifferentiableOn ℂ (fun t => (evaluationMatrix p e (F t)).det) W := by
  apply mdifferentiableOn_iff_differentiableOn.mp
  apply mdifferentiableOn_det
  intro i j
  exact mdifferentiableOn_iff_differentiableOn.mpr (h (e.symm (Pi.single j 1)) (p i))

/-- The determinant of any fixed evaluation matrix has local scalar
denominators on the full common regular locus. -/
theorem HasLocalHolomorphicNumerators.det_hasLocalDenominators
    (hF : HasLocalHolomorphicNumerators Ω F) (p : I → X) (e : V ≃ₗ[ℂ] (I → ℂ)) :
    HasLocalDenominators (fun t => (evaluationMatrix p e (F t)).det) (regularParameterSet Ω F) Ω := by
  intro z hz
  obtain ⟨W, U, a, N, hW, hWc, hzW, hWΩ, hU, hUW, hcl, ha, hN, hEq⟩ := hF z hz
  let D := regularParameterSet Ω F
  let δ (t : E) := (evaluationMatrix p e (F t)).det
  let A (t : E) := a t ^ Module.finrank ℂ V
  let H (t : E) := (evaluationMatrix p e (N t)).det
  have hA : DifferentiableOn ℂ A W := ha.pow _
  have hH : DifferentiableOn ℂ H W := differentiableOn_det_evaluationMatrix p e hN
  have hδ : DifferentiableOn ℂ δ D :=
    differentiableOn_det_evaluationMatrix p e differentiableOn_regularParameterSet
  have hUD : U ⊆ D := subset_regularParameterSet_of_numerator hWΩ hU hUW ha hN hEq
  have hAne : ∃ t ∈ W, A t ≠ 0 := by
    obtain ⟨t, _, ht⟩ := mem_closure_iff.mp (hcl hzW) univ isOpen_univ (mem_univ z)
    exact ⟨t, hUW ht, pow_ne_zero _ (hEq t ht).1⟩
  refine ⟨W, hW, hWc, hzW, A, H, hA, hAne, hH, ?_⟩
  have heq : EqOn (fun t => A t * δ t) H U := by
    intro t ht
    have hmat : evaluationMatrix p e (N t) = a t • evaluationMatrix p e (F t) := by
      rw [(hEq t ht).2]
      ext i j
      rfl
    dsimp only [A, δ, H]
    rw [hmat, det_smul, Fintype.card_fin]
  exact heq.of_subset_closure
    ((hA.continuousOn.mono inter_subset_right).mul (hδ.continuousOn.mono inter_subset_left))
    (hH.continuousOn.mono inter_subset_right) (subset_inter hUD hUW) (inter_subset_right.trans hcl)

variable [FiniteDimensional ℂ V]

/-- One injective regular member ensures an injective regular member in
every nonempty open subset of the connected parameter domain. -/
theorem HasLocalHolomorphicNumerators.exists_injective_of_open
    (hF : HasLocalHolomorphicNumerators Ω F) (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω)
    {t₀ : E} (ht₀ : t₀ ∈ Ω) (ht₀reg : t₀ ∈ regularParameterSet Ω F)
    (hinj : Function.Injective (F t₀)) {O : Set E} (hO : IsOpen O) (hOΩ : O ⊆ Ω)
    (hOne : O.Nonempty) :
    ∃ t ∈ O ∩ regularParameterSet Ω F, Function.Injective (F t) := by
  obtain ⟨p, e, hmat⟩ := exists_evaluationMatrix_eq_one (F t₀) hinj
  let δ (t : E) := (evaluationMatrix p e (F t)).det
  let D := regularParameterSet Ω F
  have hD : IsOpen D := isOpen_regularParameterSet
  have hcl : Ω ⊆ closure D := subset_closure_regularParameterSet hF
  have hδ : ContinuousOn δ D :=
    (differentiableOn_det_evaluationMatrix p e differentiableOn_regularParameterSet).continuousOn
  have hzero : HasLocalDenominators (0 : E → ℂ) univ Ω := by
    intro t ht
    exact ⟨Ω, hΩ, hΩc, ht, 1, 0, differentiableOn_const _, ⟨t, ht, one_ne_zero⟩,
      differentiableOn_const _, fun _ _ => mul_zero _⟩
  obtain ⟨t₁, ht₁⟩ := hOne
  by_contra! h
  have hneigh : ∀ᶠ t in 𝓝 t₁, t ∈ D → t ∈ (univ : Set E) → δ t = (0 : E → ℂ) t :=
    Filter.eventually_of_mem (hO.mem_nhds ht₁) fun t ht htD _ => by
      by_contra hne
      exact h t ⟨ht, htD⟩ (injective_of_det_evaluationMatrix_ne_zero p e (F t) hne)
  have hvanish := eq_of_hasLocalDenominators hΩ hΩc hD isOpen_univ hcl
    (by simp) hδ continuousOn_const (hF.det_hasLocalDenominators p e) hzero (hOΩ ht₁)
    hneigh t₀ ht₀ ht₀reg (mem_univ _)
  change (evaluationMatrix p e (F t₀)).det = (0 : ℂ) at hvanish
  rw [hmat, det_one] at hvanish
  exact one_ne_zero hvanish

end Langlands.Global.EisensteinJet

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Global.EisensteinJet

open Langlands.Analysis.Meromorphic Langlands.Automorphic.GroupSchemeFunctions
  UniformGrowthFrechetSpace

universe u

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  {N d : ℕ} (rho : Langlands.GroupScheme.MatrixRepresentation G (Fin N))
  (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth)
  (hN : 0 < N) (hrho : Langlands.GroupScheme.IsClosedSubgroup rho)

local notation "Growth[" R "," L "]" =>
  UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L

/-- The original continuation witnesses at each coordinate point give the
local numerator data needed for propagation of injectivity. -/
theorem continuedLinearCombination_hasLocalHolomorphicNumerators {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] {n : ℕ}
    (f : Fin n → E → AdelicGroupPoints F G → ℂ)
    (h : ∀ j z, ∃ B : TopologicalSpace.Opens E, z ∈ B ∧
      ∃ (R : ℝ) (L : Subgroup (FiniteAdelicGroupPoints F G)),
        IsOpen (L : Set (FiniteAdelicGroupPoints F G)) ∧
        ∃ (v : B → Growth[R, L]) (D : Set B),
          IsMeromorphicOn 𝓘(ℂ, E) v D ∧ ∀ t ∈ D,
            toFun F G rho hsmooth hcalc hN hrho R L (v t) = f j t.val) :
    HasLocalHolomorphicNumerators univ (continuedLinearCombination f) := by
  intro z _
  choose B hz R L hL v D hv hf using fun j => h j z
  obtain ⟨r, hr, S, M, _hMo, a, J, U, ha, hJ, hUo, hUball, hcl, hU⟩ :=
    exists_common_normalization_of_meromorphic F G rho hsmooth hcalc hN hrho
      z B hz R L hL v D hv f hf
  let eval : Growth[S, M] →ₗ[ℂ] (AdelicGroupPoints F G → ℂ) :=
    ⟨⟨toFun F G rho hsmooth hcalc hN hrho S M, fun _ _ => rfl⟩, fun _ _ => rfl⟩
  refine ⟨Metric.ball z r, U, a, fun t => eval.comp (J t), Metric.isOpen_ball,
    (convex_ball z r).isPreconnected, Metric.mem_ball_self hr, subset_univ _, hUo, hUball,
    hcl, ha, ?_, ?_⟩
  · intro c x
    exact hJ c (evaluation F G rho hsmooth hcalc hN hrho S M x)
  · intro t ht
    obtain ⟨_, hane, heq⟩ := hU t ht
    exact ⟨hane, LinearMap.ext heq⟩

end Langlands.Global.EisensteinJet
