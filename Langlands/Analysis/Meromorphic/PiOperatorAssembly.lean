import Langlands.Analysis.Meromorphic.AnalyticSystems
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-! # Assembling finitely many operators into an `ℓ²` product

Finitely many continuous linear maps `L ω : B → F ω` assemble into a continuous linear map
`B → PiLp 2 F`. It is compact if every `L ω` is, it is a topological embedding if
`‖x‖ ≤ C ∑_ω ‖L ω x‖`, and a family of such assemblies whose components are finite
combinations of fixed operators with holomorphic coefficients is weakly holomorphic.
-/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set

namespace Langlands.Analysis.Meromorphic

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B]
  {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {Fib : Ω → Type*} [∀ ω, NormedAddCommGroup (Fib ω)]
  [∀ ω, NormedSpace ℂ (Fib ω)]

/-- The assembly `x ↦ (L ω x)_ω` into `PiLp 2 Fib`. -/
def piAssemble (L : ∀ ω, B →L[ℂ] Fib ω) : B →L[ℂ] PiLp 2 Fib :=
  (PiLp.continuousLinearEquiv 2 ℂ Fib).symm.toContinuousLinearMap ∘L ContinuousLinearMap.pi L

@[simp] theorem piAssemble_apply (L : ∀ ω, B →L[ℂ] Fib ω) (x : B) (ω : Ω) :
    piAssemble L x ω = L ω x := rfl

/-- The inclusion of one coordinate into `PiLp 2 Fib`. -/
def piInclude (ω : Ω) : Fib ω →L[ℂ] PiLp 2 Fib :=
  (PiLp.continuousLinearEquiv 2 ℂ Fib).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.single ℂ Fib ω

theorem piAssemble_eq_sum (L : ∀ ω, B →L[ℂ] Fib ω) :
    piAssemble L = ∑ ω, piInclude ω ∘L L ω := by
  ext x ω'
  simp only [piAssemble_apply, FunLike.coe_sum, Finset.sum_apply,
    ContinuousLinearMap.coe_comp, Function.comp_apply]
  rw [show (∑ ω, piInclude (Fib := Fib) ω (L ω x)) ω' = ∑ ω, (piInclude (Fib := Fib) ω (L ω x)) ω'
    from by simp]
  simp [piInclude]

/-- An assembly of compact operators is compact. -/
theorem isCompactOperator_piAssemble (L : ∀ ω, B →L[ℂ] Fib ω)
    (h : ∀ ω, IsCompactOperator (L ω)) : IsCompactOperator (piAssemble L) := by
  rw [piAssemble_eq_sum]
  have key : ∀ s : Finset Ω, IsCompactOperator (⇑(∑ ω ∈ s, piInclude ω ∘L L ω)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using isCompactOperator_zero
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, FunLike.coe_add]
      exact ((h a).clm_comp (piInclude a)).add ih
  exact key Finset.univ

/-- If every vector is controlled by the norms of its components, the assembly is a topological
embedding. -/
theorem isEmbedding_piAssemble (L : ∀ ω, B →L[ℂ] Fib ω) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x, ‖x‖ ≤ C * ∑ ω, ‖L ω x‖) : Topology.IsEmbedding (piAssemble L) := by
  have hb : ∀ x, ‖x‖ ≤ (C * Fintype.card Ω) * ‖piAssemble L x‖ := by
    intro x
    refine (h x).trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hC
    calc ∑ ω, ‖L ω x‖ ≤ ∑ _ω : Ω, ‖piAssemble L x‖ :=
          Finset.sum_le_sum fun ω _ => by
            have := PiLp.norm_apply_le (piAssemble L x) ω
            rwa [piAssemble_apply] at this
      _ = Fintype.card Ω * ‖piAssemble L x‖ := by simp
  have hanti : AntilipschitzWith (Real.toNNReal (C * Fintype.card Ω)) (piAssemble L) := by
    refine (piAssemble L).antilipschitz_of_bound fun x => ?_
    refine (hb x).trans ?_
    gcongr
    exact Real.le_coe_toNNReal _
  exact (hanti.isUniformEmbedding (piAssemble L).uniformContinuous).isEmbedding

section Holomorphy

open scoped Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {U : Set M}

/-- The assembly of weakly holomorphic families is weakly holomorphic. -/
theorem IsHolomorphicOperatorFamilyOn.piAssemble {L : ∀ ω, M → B →L[ℂ] Fib ω}
    (hL : ∀ ω, IsHolomorphicOperatorFamilyOn I (L ω) U) :
    IsHolomorphicOperatorFamilyOn I (fun s => piAssemble fun ω => L ω s) U := by
  intro v φ
  have h := MDifferentiableOn.sum (t := Finset.univ) (fun ω _ => hL ω v (φ ∘L piInclude ω))
  refine h.congr fun s _ => ?_
  dsimp only
  rw [piAssemble_eq_sum]
  simp [Finset.sum_apply, map_sum]

end Holomorphy

end Langlands.Analysis.Meromorphic

namespace Langlands.Analysis.Meromorphic

open scoped Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {U : Set M}
  {V W X : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
  [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
  [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]

/-- A constant operator family is weakly holomorphic. -/
theorem isHolomorphicOperatorFamilyOn_const (A : V →L[ℂ] W) :
    IsHolomorphicOperatorFamilyOn I (fun _ : M => A) U :=
  fun _ _ => mdifferentiableOn_const

/-- Composing a weakly holomorphic family with a fixed operator on the left keeps it weakly
holomorphic. -/
theorem IsHolomorphicOperatorFamilyOn.clm_comp {A : M → V →L[ℂ] W}
    (hA : IsHolomorphicOperatorFamilyOn I A U) (L : W →L[ℂ] X) :
    IsHolomorphicOperatorFamilyOn I (fun s => L ∘L A s) U :=
  fun v φ => hA v (φ ∘L L)

/-- Composing a weakly holomorphic family with a fixed operator on the right keeps it weakly
holomorphic. -/
theorem IsHolomorphicOperatorFamilyOn.comp_clm {A : M → W →L[ℂ] X}
    (hA : IsHolomorphicOperatorFamilyOn I A U) (L : V →L[ℂ] W) :
    IsHolomorphicOperatorFamilyOn I (fun s => A s ∘L L) U :=
  fun v φ => hA (L v) φ

/-- A finite combination of fixed operators with holomorphic coefficients is a weakly
holomorphic operator family. -/
theorem isHolomorphicOperatorFamilyOn_sum_smul [ContinuousAdd W] [ContinuousConstSMul ℂ W]
    {κ : Type*} (t : Finset κ) (K : κ → V →L[ℂ] W) {c : κ → M → ℂ}
    (hc : ∀ j ∈ t, MDifferentiableOn I 𝓘(ℂ, ℂ) (c j) U) :
    IsHolomorphicOperatorFamilyOn I (fun s => ∑ j ∈ t, c j s • K j) U := by
  intro v φ
  have h := MDifferentiableOn.sum (t := t) (fun j hj => (hc j hj).mul
    (mdifferentiableOn_const (c := φ (K j v))))
  refine h.congr fun s _ => ?_
  simp [Finset.sum_apply, map_sum, smul_eq_mul]

/-- Sums of weakly holomorphic families are weakly holomorphic. -/
theorem IsHolomorphicOperatorFamilyOn.add [ContinuousAdd W] {A B : M → V →L[ℂ] W}
    (hA : IsHolomorphicOperatorFamilyOn I A U) (hB : IsHolomorphicOperatorFamilyOn I B U) :
    IsHolomorphicOperatorFamilyOn I (fun s => A s + B s) U := by
  intro v φ
  refine (MDifferentiableOn.add (hA v φ) (hB v φ)).congr fun s _ => ?_
  simp

end Langlands.Analysis.Meromorphic
