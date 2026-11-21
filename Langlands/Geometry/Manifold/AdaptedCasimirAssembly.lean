import Langlands.Algebra.SignedCartanCasimir
import Langlands.Geometry.Manifold.InvolutionFixedCurve
import Langlands.Geometry.Manifold.MatrixCoefficientLie
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.RCLike.Basic

/-! # Assembling an adapted Casimir element from matrix data

Let `G` be a real Lie group with a finite family of smooth matrix representations `φ v` over
real or complex fields whose differentials are jointly injective, and let `θ` be a smooth
involution of `G` with `φ v (θ g) * (φ v g)ᴴ = 1`. If every fixed point of `θ` lies in a subgroup
`K`, then the conclusion of the adapted Casimir statement holds for `G` and `K`.
-/

noncomputable section

universe u w

open scoped Manifold ContDiff TensorProduct Matrix

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Geometry.Manifold.AdaptedCasimirAssembly

open Langlands.Geometry.Manifold.MatrixCoefficientLie

section Sum

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem hasMFDerivAt_finset_sum {ι : Type*} (s : Finset ι) {f : ι → M → F} {x : M}
    {f' : ι → (TangentSpace I x →L[ℝ] F)}
    (h : ∀ i ∈ s, HasMFDerivAt I 𝓘(ℝ, F) (f i) x (f' i)) :
    HasMFDerivAt I 𝓘(ℝ, F) (fun y => ∑ i ∈ s, f i y) x (∑ i ∈ s, f' i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using hasMFDerivAt_const (I := I) (I' := 𝓘(ℝ, F)) (0 : F) x
  | insert a s ha ih =>
    have hfun : (fun y => ∑ i ∈ insert a s, f i y) = f a + fun y => ∑ i ∈ s, f i y := by
      funext y
      simp [Finset.sum_insert ha]
    rw [hfun, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end Sum

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {G : Type w} [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup 𝓘(ℝ, E) ∞ G]
  {𝕜 : Type*} [RCLike 𝕜] {N : Type*} [Fintype N] [DecidableEq N]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [LieGroup 𝓘(ℝ, E) ∞ G] in
/-- The differential of `φ ∘ θ` at the identity. -/
theorem mvfderiv_comp_theta (φ : G →* Matrix N N 𝕜)
    (hφ : ∀ a b, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, 𝕜) ∞ (fun g => φ g a b))
    (θ : G → G) (hθ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ θ) (hθ1 : θ 1 = 1)
    (a b : N) (X : GroupLieAlgebra 𝓘(ℝ, E) G) :
    mvfderiv 𝓘(ℝ, E) (fun g => φ (θ g) a b) 1 X =
      matrixDifferential 𝓘(ℝ, E) φ (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) θ 1 X) a b := by
  rw [matrixDifferential_apply]
  have h := mvfderiv_comp_apply_of_eq (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E))
    (g := fun g => φ g a b) (f := θ) (x := (1 : G)) (y := (1 : G))
    ((hφ a b).mdifferentiableAt (by simp)) (hθ.mdifferentiableAt (by simp)) hθ1 X
  exact h

omit [FiniteDimensional ℝ E] [CompleteSpace E] [LieGroup 𝓘(ℝ, E) ∞ G] in
/-- **The differential of a Cartan-type involution.** If `φ (θ g) * (φ g)ᴴ = 1` then
`D (dθ X) = -(D X)ᴴ`. -/
theorem matrixDifferential_theta (φ : G →* Matrix N N 𝕜)
    (hφ : ∀ a b, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, 𝕜) ∞ (fun g => φ g a b))
    (θ : G → G) (hθ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ θ) (hθ1 : θ 1 = 1)
    (hθφ : ∀ g, φ (θ g) * (φ g)ᴴ = 1) (X : GroupLieAlgebra 𝓘(ℝ, E) G) :
    matrixDifferential 𝓘(ℝ, E) φ (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) θ 1 X) =
      -(matrixDifferential 𝓘(ℝ, E) φ X)ᴴ := by
  ext a b
  let p : N → G → 𝕜 := fun c g => φ (θ g) a c
  let q : N → G → 𝕜 := fun c g => star (φ g b c)
  have hp_smooth (c : N) : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, 𝕜) ∞ (p c) := (hφ a c).comp hθ
  have hq_smooth (c : N) : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, 𝕜) ∞ (q c) :=
    ((RCLike.conjCLE (K := 𝕜) : 𝕜 →L[ℝ] 𝕜).contDiff (n := ∞)).contMDiff.comp (hφ b c)
  have hp (c : N) : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, 𝕜) (p c) 1
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, 𝕜) (p c) 1) :=
    ((hp_smooth c).mdifferentiableAt (by simp)).hasMFDerivAt
  have hq (c : N) : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, 𝕜) (q c) 1
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, 𝕜) (q c) 1) :=
    ((hq_smooth c).mdifferentiableAt (by simp)).hasMFDerivAt
  have hsum := hasMFDerivAt_finset_sum (I := 𝓘(ℝ, E)) Finset.univ
    (f := fun c => p c * q c) (x := (1 : G)) (fun c _ => (hp c).mul (hq c))
  have hconst : (fun g => ∑ c ∈ Finset.univ, (p c * q c) g) =
      fun _ : G => (1 : Matrix N N 𝕜) a b := by
    funext g
    have h := congrArg (fun m : Matrix N N 𝕜 => m a b) (hθφ g)
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply] at h
    simpa [p, q] using h
  rw [hconst] at hsum
  have h0 := hsum.mfderiv.symm.trans
    (hasMFDerivAt_const (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, 𝕜)) ((1 : Matrix N N 𝕜) a b) (1 : G)).mfderiv
  have e1 (c : N) : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, 𝕜) (p c) 1 X =
      matrixDifferential 𝓘(ℝ, E) φ (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) θ 1 X) a c :=
    mvfderiv_comp_theta φ hφ θ hθ hθ1 a c X
  have e2 (c : N) : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, 𝕜) (q c) 1 X =
      star (matrixDifferential 𝓘(ℝ, E) φ X b c) := by
    have h := mvfderiv_clm_comp 𝓘(ℝ, E) ((hφ b c).mdifferentiableAt (by simp) (x := (1 : G)))
      (RCLike.conjCLE (K := 𝕜) : 𝕜 →L[ℝ] 𝕜) X
    simp only [ContinuousLinearEquiv.coe_coe, RCLike.conjCLE_apply] at h
    exact h
  have ep (c : N) : p c 1 = (1 : Matrix N N 𝕜) a c := by
    simp [p, hθ1]
  have eq (c : N) : q c 1 = (1 : Matrix N N 𝕜) b c := by
    by_cases h : b = c <;> simp [q, Matrix.one_apply, h]
  have hX := congrArg (fun L : E →L[ℝ] 𝕜 => L X) h0
  simp only [_root_.sum_apply, add_apply, smul_apply, smul_eq_mul, zero_apply] at hX
  simp only [ep, eq] at hX
  simp [Finset.sum_add_distrib, Matrix.one_apply] at hX
  rw [Matrix.neg_apply, Matrix.conjTranspose_apply]
  linear_combination hX - e1 b - e2 a

omit [FiniteDimensional ℝ E] [CompleteSpace E] [LieGroup 𝓘(ℝ, E) ∞ G] [DecidableEq N] in
/-- The real trace of `A * Aᴴ` is the sum of the squared entry norms. -/
theorem re_trace_mul_conjTranspose (A : Matrix N N 𝕜) :
    RCLike.re (Matrix.trace (A * Aᴴ)) = ∑ a, ∑ b, ‖A a b‖ ^ 2 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [RCLike.star_def, RCLike.mul_conj]
  norm_cast

omit [FiniteDimensional ℝ E] [CompleteSpace E] [LieGroup 𝓘(ℝ, E) ∞ G] [DecidableEq N] in
theorem re_trace_mul_conjTranspose_pos (A : Matrix N N 𝕜) (hA : A ≠ 0) :
    0 < RCLike.re (Matrix.trace (A * Aᴴ)) := by
  rw [re_trace_mul_conjTranspose]
  obtain ⟨a, b, hab⟩ : ∃ a b, A a b ≠ 0 := by
    by_contra h
    push Not at h
    exact hA (Matrix.ext h)
  apply Finset.sum_pos' (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)
  refine ⟨a, Finset.mem_univ a, ?_⟩
  apply Finset.sum_pos' (fun _ _ => by positivity)
  exact ⟨b, Finset.mem_univ b, by positivity⟩

variable {ι : Type*} [Fintype ι] {𝕜' : ι → Type*} [∀ v, RCLike (𝕜' v)]
  {N' : ι → Type*} [∀ v, Fintype (N' v)] [∀ v, DecidableEq (N' v)]

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
/-- The real trace form of a finite family of matrix differentials. -/
def traceForm (φ : ∀ v, G →* Matrix (N' v) (N' v) (𝕜' v)) :
    LinearMap.BilinForm ℝ (GroupLieAlgebra 𝓘(ℝ, E) G) :=
  LinearMap.mk₂ ℝ
    (fun X Y => ∑ v, RCLike.re (Matrix.trace
      (matrixDifferential 𝓘(ℝ, E) (φ v) X * matrixDifferential 𝓘(ℝ, E) (φ v) Y)))
    (fun X X' Y => by
      simp only [map_add, Matrix.add_mul, Matrix.trace_add, Finset.sum_add_distrib])
    (fun c X Y => by
      simp only [map_smul, Matrix.smul_mul, Matrix.trace_smul, RCLike.smul_re, smul_eq_mul,
        Finset.mul_sum])
    (fun X Y Y' => by
      simp only [map_add, Matrix.mul_add, Matrix.trace_add, Finset.sum_add_distrib])
    (fun c X Y => by
      simp only [map_smul, Matrix.mul_smul, Matrix.trace_smul, RCLike.smul_re, smul_eq_mul,
        Finset.mul_sum])

omit [FiniteDimensional ℝ E] [CompleteSpace E] [LieGroup 𝓘(ℝ, E) ∞ G] in
theorem traceForm_apply (φ : ∀ v, G →* Matrix (N' v) (N' v) (𝕜' v))
    (X Y : GroupLieAlgebra 𝓘(ℝ, E) G) :
    traceForm φ X Y = ∑ v, RCLike.re (Matrix.trace
      (matrixDifferential 𝓘(ℝ, E) (φ v) X * matrixDifferential 𝓘(ℝ, E) (φ v) Y)) := rfl

/-- **Assembly of the adapted Casimir element.** -/
theorem exists_adapted_casimir (φ : ∀ v, G →* Matrix (N' v) (N' v) (𝕜' v))
    (hφ : ∀ v a b, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, 𝕜' v) ∞ (fun g => φ v g a b))
    (θ : G → G) (hθ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ θ) (hθθ : ∀ g, θ (θ g) = g)
    (hθ1 : θ 1 = 1) (hθφ : ∀ v g, φ v (θ g) * (φ v g)ᴴ = 1)
    (hinj : ∀ X : GroupLieAlgebra 𝓘(ℝ, E) G,
      (∀ v, matrixDifferential 𝓘(ℝ, E) (φ v) X = 0) → X = 0)
    (K : Set G) (hK : ∀ g, θ g = g → g ∈ K) :
    letI : LieGroup 𝓘(ℝ, E) (minSmoothness ℝ 3) G := LieGroup.of_le (n := ∞) (by simp)
    ∃ (n : ℕ) (X : Fin n → GroupLieAlgebra 𝓘(ℝ, E) G) (J : Finset (Fin n)),
      Submodule.span ℝ (Set.range X) = ⊤ ∧
      (∀ j ∈ J, ∃ c : ℝ → G, ContMDiff 𝓘(ℝ) 𝓘(ℝ, E) ∞ c ∧ c 0 = 1 ∧ (∀ t : ℝ, c t ∈ K) ∧
        mfderiv 𝓘(ℝ) 𝓘(ℝ, E) c 0 (1 : ℝ) = X j) ∧
      (∑ i, UniversalEnvelopingAlgebra.ι ℂ (L := ℂ ⊗[ℝ] GroupLieAlgebra 𝓘(ℝ, E) G)
            ((1 : ℂ) ⊗ₜ[ℝ] X i) ^ 2 -
          (2 : ℂ) • ∑ j ∈ J, UniversalEnvelopingAlgebra.ι ℂ
            (L := ℂ ⊗[ℝ] GroupLieAlgebra 𝓘(ℝ, E) G) ((1 : ℂ) ⊗ₜ[ℝ] X j) ^ 2) ∈
        Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] GroupLieAlgebra 𝓘(ℝ, E) G)) := by
  let : LieGroup 𝓘(ℝ, E) (minSmoothness ℝ 3) G := LieGroup.of_le (n := ∞) (by simp)
  have : FiniteDimensional ℝ (GroupLieAlgebra 𝓘(ℝ, E) G) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let D := fun v => matrixDifferential 𝓘(ℝ, E) (φ v)
  let dθ : GroupLieAlgebra 𝓘(ℝ, E) G →L[ℝ] GroupLieAlgebra 𝓘(ℝ, E) G :=
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) θ 1
  have hDθ (v : ι) (X : GroupLieAlgebra 𝓘(ℝ, E) G) : D v (dθ X) = -(D v X)ᴴ :=
    matrixDifferential_theta (φ v) (hφ v) θ hθ hθ1 (hθφ v) X
  have hdθdθ (X : GroupLieAlgebra 𝓘(ℝ, E) G) : dθ (dθ X) = X := by
    apply sub_eq_zero.mp
    apply hinj
    intro v
    change D v (dθ (dθ X) - X) = 0
    rw [map_sub, hDθ, hDθ]
    simp
  let s : GroupLieAlgebra 𝓘(ℝ, E) G →ₗ[ℝ] GroupLieAlgebra 𝓘(ℝ, E) G := -(dθ : _ →ₗ[ℝ] _)
  have hs_apply (X : GroupLieAlgebra 𝓘(ℝ, E) G) : s X = -dθ X := rfl
  have hDs (v : ι) (X : GroupLieAlgebra 𝓘(ℝ, E) G) : D v (s X) = (D v X)ᴴ := by
    rw [hs_apply, map_neg, hDθ, neg_neg]
  let B := traceForm (E := E) (G := G) φ
  have hsymm : ∀ X Y, B X Y = B Y X := by
    intro X Y
    simp only [B, traceForm_apply]
    exact Finset.sum_congr rfl fun v _ => by rw [Matrix.trace_mul_comm]
  have hInv : ∀ X Y Z, B ⁅X, Y⁆ Z = B X ⁅Y, Z⁆ := by
    intro X Y Z
    simp only [B, traceForm_apply]
    apply Finset.sum_congr rfl
    intro v _
    rw [matrixDifferential_lie (I := 𝓘(ℝ, E)) (φ v) (hφ v),
      matrixDifferential_lie (I := 𝓘(ℝ, E)) (φ v) (hφ v)]
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub, Matrix.trace_sub]
    set A := matrixDifferential 𝓘(ℝ, E) (φ v) X
    set A' := matrixDifferential 𝓘(ℝ, E) (φ v) Y
    set A'' := matrixDifferential 𝓘(ℝ, E) (φ v) Z
    rw [Matrix.mul_assoc A A' A'', Matrix.mul_assoc A' A A'', Matrix.trace_mul_comm A',
      Matrix.mul_assoc]
  have hs : ∀ X, s (s X) = X := by
    intro X
    rw [hs_apply, hs_apply, map_neg, neg_neg, hdθdθ]
  have hBs : ∀ X Y, B (s X) (s Y) = B X Y := by
    intro X Y
    simp only [B, traceForm_apply]
    apply Finset.sum_congr rfl
    intro v _
    change RCLike.re (Matrix.trace (D v (s X) * D v (s Y))) =
      RCLike.re (Matrix.trace (D v X * D v Y))
    rw [hDs, hDs, ← Matrix.conjTranspose_mul, Matrix.trace_conjTranspose, RCLike.star_def,
      RCLike.conj_re, Matrix.trace_mul_comm]
  have hpos : ∀ X, X ≠ 0 → 0 < B X (s X) := by
    intro X hX
    simp only [B, traceForm_apply]
    have hne : ∃ v, D v X ≠ 0 := by
      by_contra h
      push Not at h
      exact hX (hinj X h)
    obtain ⟨v, hv⟩ := hne
    refine Finset.sum_pos' (fun w _ => ?_) ⟨v, Finset.mem_univ v, ?_⟩
    · change 0 ≤ RCLike.re (Matrix.trace (D w X * D w (s X)))
      rw [hDs, re_trace_mul_conjTranspose]
      positivity
    · change 0 < RCLike.re (Matrix.trace (D v X * D v (s X)))
      rw [hDs]
      exact re_trace_mul_conjTranspose_pos _ hv
  obtain ⟨n, X, J, hspan, hJ, hcent⟩ :=
    Langlands.Algebra.SignedCartanCasimir.exists_signed_casimir B hsymm hInv s hs hBs hpos
  refine ⟨n, X, J, hspan, ?_, hcent⟩
  intro j hj
  have hfix : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) θ 1 (X j) = X j := by
    have h := hJ j hj
    rw [hs_apply, neg_inj] at h
    exact h
  obtain ⟨c, hc, hc0, hcfix, hcv⟩ :=
    InvolutionFixedCurve.exists_contMDiff_curve_fixed θ hθ hθθ 1 hθ1 (X j) hfix
  exact ⟨c, hc, hc0, fun t => hK _ (hcfix t), hcv⟩

end Langlands.Geometry.Manifold.AdaptedCasimirAssembly
