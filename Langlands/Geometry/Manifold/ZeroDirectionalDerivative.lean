import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Algebra.MvPolynomial.Basic

/-! # Functions with vanishing derivative in a fixed tangent direction

For a point `x` of a manifold and a tangent vector `X` at `x`, the functions into a real normed
commutative algebra that are differentiable at `x` with derivative zero in direction `X` are closed
under constants, sums, products, polynomial expressions, continuous linear maps, local equality and
quotients by functions that do not vanish at `x`.
-/

noncomputable section

open scoped Manifold ContDiff Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Geometry.Manifold.ZeroDirectionalDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {x : M} (X : TangentSpace I x)
  {K : Type*} [NormedCommRing K] [NormedAlgebra ℝ K]

/-- `h` has a manifold derivative at `x` that vanishes in direction `X`. -/
def ZeroDeriv (h : M → K) : Prop :=
  ∃ h' : E →L[ℝ] K, HasMFDerivAt I 𝓘(ℝ, K) h x h' ∧ h' X = 0

variable {X}

theorem zeroDeriv_const (c : K) : ZeroDeriv X (fun _ : M => c) :=
  ⟨0, hasMFDerivAt_const (I := I) (I' := 𝓘(ℝ, K)) c x, rfl⟩

theorem ZeroDeriv.add {f g : M → K} (hf : ZeroDeriv X f) (hg : ZeroDeriv X g) :
    ZeroDeriv X (fun y => f y + g y) := by
  obtain ⟨f', hf', hfX⟩ := hf
  obtain ⟨g', hg', hgX⟩ := hg
  refine ⟨f' + g', hf'.add hg', ?_⟩
  change f' X + g' X = 0
  rw [hfX, hgX, add_zero]

theorem ZeroDeriv.mul {f g : M → K} (hf : ZeroDeriv X f) (hg : ZeroDeriv X g) :
    ZeroDeriv X (fun y => f y * g y) := by
  obtain ⟨f', hf', hfX⟩ := hf
  obtain ⟨g', hg', hgX⟩ := hg
  refine ⟨f x • g' + g x • f', hf'.mul hg', ?_⟩
  change f x • g' X + g x • f' X = 0
  rw [hfX, hgX, smul_zero, smul_zero, add_zero]

theorem zeroDeriv_finset_sum {ι : Type*} (s : Finset ι) {f : ι → M → K}
    (hf : ∀ i ∈ s, ZeroDeriv X (f i)) : ZeroDeriv X (fun y => ∑ i ∈ s, f i y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zeroDeriv_const (X := X) (0 : K)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem zeroDeriv_aeval {σ : Type*} {R : Type*} [CommRing R] [Algebra R K]
    {f : σ → M → K} (hf : ∀ s, ZeroDeriv X (f s)) (P : MvPolynomial σ R) :
    ZeroDeriv X (fun y => MvPolynomial.aeval (fun s => f s y) P) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    simpa only [MvPolynomial.aeval_C] using zeroDeriv_const (X := X) (algebraMap R K a)
  | add p q hp hq =>
    simpa only [map_add] using hp.add hq
  | mul_X p s hp =>
    simpa only [map_mul, MvPolynomial.aeval_X] using hp.mul (hf s)

theorem ZeroDeriv.congr {f g : M → K} (hf : ZeroDeriv X f) (hfg : f =ᶠ[𝓝 x] g) :
    ZeroDeriv X g := by
  obtain ⟨f', hf', hfX⟩ := hf
  exact ⟨f', hf'.congr_of_eventuallyEq hfg.symm, hfX⟩

theorem ZeroDeriv.clm {F : Type*} [NormedCommRing F] [NormedAlgebra ℝ F] {f : M → K}
    (hf : ZeroDeriv X f) (L : K →L[ℝ] F) : ZeroDeriv X (fun y => L (f y)) := by
  obtain ⟨f', hf', hfX⟩ := hf
  refine ⟨L.comp f', (L.hasMFDerivAt (x := f x)).comp x hf', ?_⟩
  change L (f' X) = 0
  rw [hfX, map_zero]

/-- A quotient of functions with zero derivative, by a function nonzero at `x`. -/
theorem ZeroDeriv.div {𝕂 : Type*} [NormedField 𝕂] [NormedAlgebra ℝ 𝕂] {f g : M → 𝕂}
    (hf : ZeroDeriv X f) (hg : ZeroDeriv X g) (hgx : g x ≠ 0)
    (hd : MDifferentiableAt I 𝓘(ℝ, 𝕂) (fun y => f y / g y) x) :
    ZeroDeriv X (fun y => f y / g y) := by
  obtain ⟨f', hf', hfX⟩ := hf
  obtain ⟨g', hg', hgX⟩ := hg
  let q' : E →L[ℝ] 𝕂 := mfderiv I 𝓘(ℝ, 𝕂) (fun y => f y / g y) x
  have hq : HasMFDerivAt I 𝓘(ℝ, 𝕂) (fun y => f y / g y) x q' := hd.hasMFDerivAt
  refine ⟨q', hq, ?_⟩
  have hprod : (fun y => f y / g y) * g =ᶠ[𝓝 x] f := by
    have hcont : ContinuousAt g x := hg'.continuousAt
    filter_upwards [hcont.eventually_ne hgx] with y hy
    exact div_mul_cancel₀ (f y) hy
  have h1 := (hq.mul hg').congr_of_eventuallyEq hprod.symm
  have h2 := h1.mfderiv.symm.trans hf'.mfderiv
  have h3 := congrArg (fun L => L X) h2
  change (f x / g x) • g' X + g x • q' X = f' X at h3
  rw [hgX, hfX, smul_zero, zero_add, smul_eq_mul] at h3
  exact (mul_eq_zero.mp h3).resolve_left hgx

theorem hasMFDerivAt_finset_sum' {ι : Type*} (s : Finset ι) {f : ι → M → K}
    {f' : ι → (TangentSpace I x →L[ℝ] K)}
    (h : ∀ i ∈ s, HasMFDerivAt I 𝓘(ℝ, K) (f i) x (f' i)) :
    HasMFDerivAt I 𝓘(ℝ, K) (fun y => ∑ i ∈ s, f i y) x (∑ i ∈ s, f' i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using hasMFDerivAt_const (I := I) (I' := 𝓘(ℝ, K)) (0 : K) x
  | insert a s ha ih =>
    have hfun : (fun y => ∑ i ∈ insert a s, f i y) = f a + fun y => ∑ i ∈ s, f i y := by
      funext y
      simp [Finset.sum_insert ha]
    rw [hfun, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- If `A * B = 1` pointwise, `A x = 1`, the entries of `A` have zero derivative in direction `X`
and those of `B` are differentiable at `x`, then the entries of `B` have zero derivative too. -/
theorem zeroDeriv_of_mul_eq_one {n : Type*} [Fintype n] [DecidableEq n]
    {A B : M → Matrix n n K} (hAB : ∀ y, A y * B y = 1) (hA1 : A x = 1)
    (hA : ∀ i j, ZeroDeriv X (fun y => A y i j))
    (hB : ∀ i j, MDifferentiableAt I 𝓘(ℝ, K) (fun y => B y i j) x) (i j : n) :
    ZeroDeriv X (fun y => B y i j) := by
  classical
  choose a' ha' haX using hA
  let b' : n → n → (E →L[ℝ] K) := fun k l => mfderiv I 𝓘(ℝ, K) (fun y => B y k l) x
  have hb' (k l : n) : HasMFDerivAt I 𝓘(ℝ, K) (fun y => B y k l) x (b' k l) :=
    (hB k l).hasMFDerivAt
  refine ⟨b' i j, hb' i j, ?_⟩
  have hsum := hasMFDerivAt_finset_sum' (I := I) Finset.univ
    (f := fun k y => A y i k * B y k j) (x := x)
    (fun k _ => (ha' i k).mul (hb' k j))
  have hconst : (fun y => ∑ k ∈ Finset.univ, A y i k * B y k j) = fun _ => (1 : Matrix n n K) i j := by
    funext y
    rw [← hAB y, Matrix.mul_apply]
  rw [hconst] at hsum
  have h0 := hsum.mfderiv.symm.trans
    (hasMFDerivAt_const (I := I) (I' := 𝓘(ℝ, K)) ((1 : Matrix n n K) i j) x).mfderiv
  have h1 := congrArg (fun L : E →L[ℝ] K => L X) h0
  simp only [_root_.sum_apply, add_apply, smul_apply, smul_eq_mul, zero_apply] at h1
  simp only [haX, mul_zero, add_zero, hA1, Matrix.one_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte] at h1
  exact h1

end Langlands.Geometry.Manifold.ZeroDirectionalDerivative
