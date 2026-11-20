import Langlands.Analysis.Meromorphic.WeakComposition
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-! # Local reduction of an analytic system to a square system

Bernstein–Lapid, Appendix A: in a holomorphic frame `ℓ s : ℂⁿ → V`, choose `n`
scalar equations, with coefficient matrix `A(s) = scalarMatrix μ ℓ a s`. The
determinant `det A` and the adjugate solution `u = ℓ (adj A · b)` are
holomorphic (given Hartogs's theorem as the premise `HartogsDiagonal E`), and
every solution `x` at a parameter `s` satisfies `det A(s) • x = u s`. At a
parameter with a unique solution some choice has `det A ≠ 0`. -/

noncomputable section
set_option autoImplicit false

namespace Langlands.Analysis.Meromorphic

open Set Filter Topology Matrix
open scoped Manifold

section LinearAlgebra

/-- A continuous linear map on `ℂⁿ` expanded along the standard basis. -/
theorem clm_apply_eq_sum {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] {n : ℕ}
    (L : (Fin n → ℂ) →L[ℂ] V) (z : Fin n → ℂ) :
    L z = ∑ k, z k • L (Pi.single k 1) := by
  conv_lhs => rw [pi_eq_sum_univ' z]
  rw [map_sum]
  simp only [map_smul]

/-- A continuous linear form composed with a continuous linear map on `ℂⁿ`,
expanded along the standard basis. -/
theorem clm_apply_eq_sum_mul {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    {n : ℕ} (ψ : V →L[ℂ] ℂ) (L : (Fin n → ℂ) →L[ℂ] V) (z : Fin n → ℂ) :
    ψ (L z) = ∑ k, z k * ψ (L (Pi.single k 1)) := by
  rw [clm_apply_eq_sum L z, map_sum]
  simp only [map_smul, smul_eq_mul]

/-- If the vectors `r a ∈ ℂⁿ` have no common orthogonal vector other than `0`,
then `n` of them form an invertible matrix. -/
theorem exists_det_ne_zero {α : Type*} {n : ℕ} (r : α → Fin n → ℂ)
    (h : ∀ z : Fin n → ℂ, (∀ a, r a ⬝ᵥ z = 0) → z = 0) :
    ∃ a : Fin n → α, (Matrix.of fun j k => r (a j) k).det ≠ 0 := by
  classical
  have hspan : Submodule.span ℂ (Set.range r) = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hfle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    have key : ∀ x : Fin n → ℂ, f x = x ⬝ᵥ fun k => f (Pi.single k 1) := by
      intro x
      conv_lhs => rw [pi_eq_sum_univ' x]
      simp [map_sum, dotProduct]
    have hz : (fun k => f (Pi.single k 1)) = 0 := by
      refine h _ fun a => ?_
      rw [← key]
      exact LinearMap.mem_ker.1 (hfle (Submodule.subset_span ⟨a, rfl⟩))
    exact hf0 (LinearMap.ext fun x => by rw [key x, hz]; simp)
  obtain ⟨κ, a, -, hsp, hli⟩ := exists_linearIndependent' ℂ r
  have htop : ⊤ ≤ Submodule.span ℂ (Set.range (r ∘ a)) := by rw [hsp, hspan]
  let b := Module.Basis.mk hli htop
  have : Finite κ := Module.Finite.finite_basis b
  have hcard : Nat.card κ = n := by
    rw [← Module.finrank_eq_nat_card_basis b, Module.finrank_fin_fun]
  let e : κ ≃ Fin n := Finite.equivFinOfCardEq hcard
  refine ⟨a ∘ e.symm, ?_⟩
  have hli' : LinearIndependent ℂ ((r ∘ a) ∘ e.symm) := hli.comp _ e.symm.injective
  have hu : IsUnit (Matrix.of fun j k => r ((a ∘ e.symm) j) k) := by
    rw [← Matrix.linearIndependent_rows_iff_isUnit]
    exact hli'
  exact ((Matrix.isUnit_iff_isUnit_det _).1 hu).ne_zero

end LinearAlgebra

section Holomorphy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

/-- A finite sum of holomorphic scalar functions is holomorphic. -/
theorem mdifferentiableOn_finset_sum {α : Type*} (t : Finset α) {f : α → M → ℂ} {W : Set M}
    (hf : ∀ a ∈ t, MDifferentiableOn 𝓘(ℂ, E) 𝓘(ℂ, ℂ) (f a) W) :
    MDifferentiableOn 𝓘(ℂ, E) 𝓘(ℂ, ℂ) (fun s => ∑ a ∈ t, f a s) W := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    simpa using (mdifferentiableOn_const : MDifferentiableOn 𝓘(ℂ, E) 𝓘(ℂ, ℂ)
      (fun _ : M => (0 : ℂ)) W)
  | insert a t ha IH =>
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a t)).add
      (IH fun b hb => hf b (Finset.mem_insert_of_mem hb))

/-- A finite product of holomorphic scalar functions is holomorphic. -/
theorem mdifferentiableOn_finset_prod {α : Type*} (t : Finset α) {f : α → M → ℂ} {W : Set M}
    (hf : ∀ a ∈ t, MDifferentiableOn 𝓘(ℂ, E) 𝓘(ℂ, ℂ) (f a) W) :
    MDifferentiableOn 𝓘(ℂ, E) 𝓘(ℂ, ℂ) (fun s => ∏ a ∈ t, f a s) W := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    simpa using (mdifferentiableOn_const : MDifferentiableOn 𝓘(ℂ, E) 𝓘(ℂ, ℂ)
      (fun _ : M => (1 : ℂ)) W)
  | insert a t ha IH =>
    simp only [Finset.prod_insert ha]
    exact (hf a (Finset.mem_insert_self a t)).mul
      (IH fun b hb => hf b (Finset.mem_insert_of_mem hb))

/-- The determinant of a matrix of holomorphic functions is holomorphic. -/
theorem mdifferentiableOn_det {m : Type*} [Fintype m] [DecidableEq m]
    {A : M → Matrix m m ℂ} {W : Set M}
    (hA : ∀ j k, MDifferentiableOn 𝓘(ℂ, E) 𝓘(ℂ, ℂ) (fun s => A s j k) W) :
    MDifferentiableOn 𝓘(ℂ, E) 𝓘(ℂ, ℂ) (fun s => (A s).det) W := by
  simp only [Matrix.det_apply']
  refine mdifferentiableOn_finset_sum (f := fun σ s => (Equiv.Perm.sign σ : ℂ) *
    ∏ i, A s (σ i) i) _ fun σ _ => ?_
  exact (mdifferentiableOn_const).mul
    (mdifferentiableOn_finset_prod (f := fun i s => A s (σ i) i) _ fun i _ => hA _ _)

/-- The entries of the adjugate of a matrix of holomorphic functions are
holomorphic. -/
theorem mdifferentiableOn_adjugate {m : Type*} [Fintype m] [DecidableEq m]
    {A : M → Matrix m m ℂ} {W : Set M}
    (hA : ∀ j k, MDifferentiableOn 𝓘(ℂ, E) 𝓘(ℂ, ℂ) (fun s => A s j k) W) (j k : m) :
    MDifferentiableOn 𝓘(ℂ, E) 𝓘(ℂ, ℂ) (fun s => (A s).adjugate j k) W := by
  simp only [Matrix.adjugate_apply]
  refine mdifferentiableOn_det fun p q => ?_
  by_cases hp : p = k
  · exact (mdifferentiableOn_const (c := (Pi.single j 1 : m → ℂ) q)).congr fun s _ => by
      simp [Matrix.updateRow_apply, hp]
  · exact (hA p q).congr fun s _ => by simp [Matrix.updateRow_apply, hp]

end Holomorphy

section ScalarEquations

variable {M : Type*} {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
  {ι : Type*} {F : ι → Type*} [∀ i, AddCommGroup (F i)] [∀ i, Module ℂ (F i)]
  [∀ i, TopologicalSpace (F i)]

/-- The coefficient matrix of the `n` scalar equations `(a j).2 (μ (a j).1 s v) = (a j).2 (c (a j).1 s)`
in the unknown `v = ℓ s z`, `z ∈ ℂⁿ`: its `(j, k)` entry is
`(a j).2 (μ (a j).1 s (ℓ s eₖ))`. -/
def scalarMatrix {n : ℕ} (μ : ∀ i, M → V →L[ℂ] F i) (ℓ : M → (Fin n → ℂ) →L[ℂ] V)
    (a : Fin n → Σ i, (F i →L[ℂ] ℂ)) (s : M) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun j k => (a j).2 (μ (a j).1 s (ℓ s (Pi.single k 1)))

/-- The right-hand side `j ↦ (a j).2 (c (a j).1 s)` of the scalar equations `a`. -/
def scalarVector {n : ℕ} (c : ∀ i, M → F i) (a : Fin n → Σ i, (F i →L[ℂ] ℂ)) (s : M) :
    Fin n → ℂ :=
  fun j => (a j).2 (c (a j).1 s)

/-- The adjugate solution `ℓ s (adj A(s) · b(s))` of the scalar equations `a`,
where `A = scalarMatrix μ ℓ a` and `b = scalarVector c a`. -/
def adjugateSolution {n : ℕ} (μ : ∀ i, M → V →L[ℂ] F i) (c : ∀ i, M → F i)
    (ℓ : M → (Fin n → ℂ) →L[ℂ] V) (a : Fin n → Σ i, (F i →L[ℂ] ℂ)) (s : M) : V :=
  ℓ s ((scalarMatrix μ ℓ a s).adjugate *ᵥ scalarVector c a s)

/-- Cramer's rule in adjugate form: if every solution at `s` lies in the range of
`ℓ s`, then `det A(s) • x = adjugateSolution μ c ℓ a s` for every solution `x`. -/
theorem det_smul_eq_adjugateSolution {n : ℕ} {μ : ∀ i, M → V →L[ℂ] F i}
    {c : ∀ i, M → F i} {ℓ : M → (Fin n → ℂ) →L[ℂ] V} (a : Fin n → Σ i, (F i →L[ℂ] ℂ))
    {s : M} (hrange : systemSolutions μ c s ⊆ Set.range (ℓ s)) {x : V}
    (hx : x ∈ systemSolutions μ c s) :
    (scalarMatrix μ ℓ a s).det • x = adjugateSolution μ c ℓ a s := by
  obtain ⟨z, rfl⟩ := hrange hx
  have hAz : scalarMatrix μ ℓ a s *ᵥ z = scalarVector c a s := by
    funext j
    simp only [Matrix.mulVec, dotProduct, scalarMatrix, scalarVector, Matrix.of_apply]
    rw [← hx (a j).1, clm_apply_eq_sum (ℓ s) z, map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, map_smul, smul_eq_mul, mul_comm]
  have hyz : (scalarMatrix μ ℓ a s).adjugate *ᵥ scalarVector c a s =
      (scalarMatrix μ ℓ a s).det • z := by
    rw [← hAz, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec,
      Matrix.one_mulVec]
  simp only [adjugateSolution, hyz, map_smul]

end ScalarEquations

section LocalSolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) 1 M]
  {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
  {ι : Type*} {F : ι → Type*} [∀ i, AddCommGroup (F i)] [∀ i, Module ℂ (F i)]
  [∀ i, TopologicalSpace (F i)]

/-- The entries of `scalarMatrix μ ℓ a` are holomorphic on an open set where `ℓ`
is holomorphic (Bernstein–Lapid §3.2, via Hartogs's theorem). -/
theorem mdifferentiableOn_scalarMatrix (hH : HartogsDiagonal E)
    {μ : ∀ i, M → V →L[ℂ] F i} {c : ∀ i, M → F i} (hsys : IsAnalyticSystem 𝓘(ℂ, E) μ c)
    {n : ℕ} {ℓ : M → (Fin n → ℂ) →L[ℂ] V} {W : Set M} (hW : IsOpen W)
    (hℓ : IsHolomorphicOperatorFamilyOn 𝓘(ℂ, E) ℓ W) (a : Fin n → Σ i, (F i →L[ℂ] ℂ))
    (j k : Fin n) :
    MDifferentiableOn 𝓘(ℂ, E) 𝓘(ℂ, ℂ) (fun s => scalarMatrix μ ℓ a s j k) W :=
  mdifferentiableOn_apply_apply hH hW (fun v φ => (hsys.1 (a j).1 v φ).mono (subset_univ W))
    (hℓ (Pi.single k 1)) (a j).2

/-- The determinant of `scalarMatrix μ ℓ a` is holomorphic on `W`. -/
theorem mdifferentiableOn_det_scalarMatrix (hH : HartogsDiagonal E)
    {μ : ∀ i, M → V →L[ℂ] F i} {c : ∀ i, M → F i} (hsys : IsAnalyticSystem 𝓘(ℂ, E) μ c)
    {n : ℕ} {ℓ : M → (Fin n → ℂ) →L[ℂ] V} {W : Set M} (hW : IsOpen W)
    (hℓ : IsHolomorphicOperatorFamilyOn 𝓘(ℂ, E) ℓ W) (a : Fin n → Σ i, (F i →L[ℂ] ℂ)) :
    MDifferentiableOn 𝓘(ℂ, E) 𝓘(ℂ, ℂ) (fun s => (scalarMatrix μ ℓ a s).det) W :=
  mdifferentiableOn_det (mdifferentiableOn_scalarMatrix hH hsys hW hℓ a)

/-- The coordinates of the adjugate solution, `adj A(s) · b(s)`, are holomorphic on `W`. -/
theorem mdifferentiableOn_adjugate_mulVec (hH : HartogsDiagonal E)
    {μ : ∀ i, M → V →L[ℂ] F i} {c : ∀ i, M → F i} (hsys : IsAnalyticSystem 𝓘(ℂ, E) μ c)
    {n : ℕ} {ℓ : M → (Fin n → ℂ) →L[ℂ] V} {W : Set M} (hW : IsOpen W)
    (hℓ : IsHolomorphicOperatorFamilyOn 𝓘(ℂ, E) ℓ W) (a : Fin n → Σ i, (F i →L[ℂ] ℂ))
    (k : Fin n) :
    MDifferentiableOn 𝓘(ℂ, E) 𝓘(ℂ, ℂ)
      (fun s => ((scalarMatrix μ ℓ a s).adjugate *ᵥ scalarVector c a s) k) W := by
  classical
  refine (mdifferentiableOn_finset_sum
    (f := fun j s => (scalarMatrix μ ℓ a s).adjugate k j * scalarVector c a s j)
    Finset.univ fun j _ => (mdifferentiableOn_adjugate
      (mdifferentiableOn_scalarMatrix hH hsys hW hℓ a) k j).mul
      ((hsys.2 (a j).1 (a j).2).mono (subset_univ W))).congr fun s _ => ?_
  simp only [Matrix.mulVec, dotProduct]

/-- The adjugate solution is holomorphic on `W`. -/
theorem isHolomorphicOn_adjugateSolution (hH : HartogsDiagonal E)
    {μ : ∀ i, M → V →L[ℂ] F i} {c : ∀ i, M → F i} (hsys : IsAnalyticSystem 𝓘(ℂ, E) μ c)
    {n : ℕ} {ℓ : M → (Fin n → ℂ) →L[ℂ] V} {W : Set M} (hW : IsOpen W)
    (hℓ : IsHolomorphicOperatorFamilyOn 𝓘(ℂ, E) ℓ W) (a : Fin n → Σ i, (F i →L[ℂ] ℂ)) :
    IsHolomorphicOn 𝓘(ℂ, E) (adjugateSolution μ c ℓ a) W := by
  intro φ
  refine (mdifferentiableOn_finset_sum
    (f := fun k s => ((scalarMatrix μ ℓ a s).adjugate *ᵥ scalarVector c a s) k *
      φ (ℓ s (Pi.single k 1))) Finset.univ fun k _ =>
      (mdifferentiableOn_adjugate_mulVec hH hsys hW hℓ a k).mul
      (hℓ (Pi.single k 1) φ)).congr fun s _ => ?_
  exact clm_apply_eq_sum_mul φ (ℓ s) _

/-- The scalarized residuals `φ (μ i s (u s)) - det A(s) * φ (c i s)` of the
adjugate solution `u` are holomorphic on `W`. -/
theorem mdifferentiableOn_residual (hH : HartogsDiagonal E)
    {μ : ∀ i, M → V →L[ℂ] F i} {c : ∀ i, M → F i} (hsys : IsAnalyticSystem 𝓘(ℂ, E) μ c)
    {n : ℕ} {ℓ : M → (Fin n → ℂ) →L[ℂ] V} {W : Set M} (hW : IsOpen W)
    (hℓ : IsHolomorphicOperatorFamilyOn 𝓘(ℂ, E) ℓ W) (a : Fin n → Σ i, (F i →L[ℂ] ℂ))
    (i : ι) (φ : F i →L[ℂ] ℂ) :
    MDifferentiableOn 𝓘(ℂ, E) 𝓘(ℂ, ℂ) (fun s => φ (μ i s (adjugateSolution μ c ℓ a s)) -
      (scalarMatrix μ ℓ a s).det * φ (c i s)) W := by
  refine ((mdifferentiableOn_finset_sum
    (f := fun k s => ((scalarMatrix μ ℓ a s).adjugate *ᵥ scalarVector c a s) k *
      φ (μ i s (ℓ s (Pi.single k 1)))) Finset.univ
    fun k _ => (mdifferentiableOn_adjugate_mulVec hH hsys hW hℓ a k).mul
      (mdifferentiableOn_apply_apply hH hW (fun v ψ => (hsys.1 i v ψ).mono (subset_univ W))
        (hℓ (Pi.single k 1)) φ)).sub
    ((mdifferentiableOn_det_scalarMatrix hH hsys hW hℓ a).mul
      ((hsys.2 i φ).mono (subset_univ W)))).congr fun s _ => ?_
  have h := clm_apply_eq_sum_mul φ ((μ i s).comp (ℓ s))
    ((scalarMatrix μ ℓ a s).adjugate *ᵥ scalarVector c a s)
  simp only [ContinuousLinearMap.comp_apply] at h
  simp only [adjugateSolution, h, Pi.sub_apply, Pi.mul_apply]

end LocalSolution

section UniqueSolution

variable {M : Type*} {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
  {ι : Type*} {F : ι → Type*} [∀ i, AddCommGroup (F i)] [∀ i, Module ℂ (F i)]
  [∀ i, Module ℝ (F i)] [∀ i, IsScalarTower ℝ ℂ (F i)] [∀ i, TopologicalSpace (F i)]
  [∀ i, IsTopologicalAddGroup (F i)] [∀ i, ContinuousSMul ℂ (F i)]
  [∀ i, LocallyConvexSpace ℝ (F i)] [∀ i, T2Space (F i)]

/-- Bernstein–Lapid, Appendix A: at a parameter `s₁` where the system has a unique
solution and `ℓ s₁` is injective with the solution in its range, some `n` scalar
equations have an invertible coefficient matrix at `s₁`. -/
theorem exists_det_scalarMatrix_ne_zero {μ : ∀ i, M → V →L[ℂ] F i} {c : ∀ i, M → F i}
    {n : ℕ} {ℓ : M → (Fin n → ℂ) →L[ℂ] V} {s₁ : M} (hinj : Function.Injective (ℓ s₁))
    (hs₁ : s₁ ∈ uniqueSolutionLocus μ c) :
    ∃ a : Fin n → Σ i, (F i →L[ℂ] ℂ), (scalarMatrix μ ℓ a s₁).det ≠ 0 := by
  obtain ⟨v₁, hv₁⟩ := hs₁
  let r : (Σ i, (F i →L[ℂ] ℂ)) → Fin n → ℂ :=
    fun a k => a.2 (μ a.1 s₁ (ℓ s₁ (Pi.single k 1)))
  have hr : ∀ z : Fin n → ℂ, (∀ a, r a ⬝ᵥ z = 0) → z = 0 := by
    intro z hz
    have hrz : ∀ a : Σ i, (F i →L[ℂ] ℂ), a.2 (μ a.1 s₁ (ℓ s₁ z)) = 0 := by
      intro a
      have h0 := hz a
      simp only [dotProduct, r] at h0
      rw [clm_apply_eq_sum (ℓ s₁) z, map_sum, map_sum, ← h0]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul, map_smul, smul_eq_mul, mul_comm]
    have hμz : ∀ i, μ i s₁ (ℓ s₁ z) = 0 := fun i =>
      eq_of_forall_clm_apply_eq fun φ => by simpa using hrz ⟨i, φ⟩
    have hv : v₁ ∈ systemSolutions μ c s₁ := by rw [hv₁]; rfl
    have hsol : v₁ + ℓ s₁ z ∈ systemSolutions μ c s₁ := by
      intro i
      rw [map_add, hμz i, add_zero]
      exact hv i
    rw [hv₁] at hsol
    have hℓz : ℓ s₁ z = 0 := by simpa using hsol
    exact hinj (by rw [hℓz, map_zero])
  exact exists_det_ne_zero r hr

end UniqueSolution

end Langlands.Analysis.Meromorphic
