import Langlands.Analysis.Meromorphic.LocalScalarization

/-! # Holomorphic recovery in a finite frame

Scalar tests that separate the coefficients of a holomorphic finite frame at one point
recover a weakly holomorphic extension near that point by finite matrix inversion.
-/

noncomputable section
set_option autoImplicit false

namespace Langlands.Analysis.Meromorphic

open Set Matrix
open scoped Manifold

/-- The vector recovered from a finite frame, a square family of scalar tests, and
the prescribed vector of test values, by dividing the adjugate by the determinant. -/
def recoverFromFrameTests {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    {n : ℕ} (ℓ : (Fin n → ℂ) →L[ℂ] V) (μ : Fin n → V →L[ℂ] ℂ) (b : Fin n → ℂ) : V :=
  let A : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun j k => μ j (ℓ (Pi.single k 1))
  ℓ (A.det⁻¹ • (A.adjugate *ᵥ b))

variable {E M V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]

/-- If parameter-dependent scalar tests are holomorphic on the columns of a frame and
separate its coefficients at `s₀`, scalar holomorphic extensions of `p s * μ i s (v s)`
recover one weakly holomorphic extension of `p s • v s` near `s₀`. The values of `v`
need only be in the frame range on the agreement set `W ∩ D`. The neighborhoods
of the scalar extensions may depend on the test. -/
theorem exists_isHolomorphicOn_smul_of_frame_tests
    {n : ℕ} {ℓ : M → (Fin n → ℂ) →L[ℂ] V} {W D : Set M} {s₀ : M}
    (hW : IsOpen W) (hs₀ : s₀ ∈ W)
    (hℓ : IsHolomorphicOperatorFamilyOn 𝓘(ℂ, E) ℓ W)
    {ι : Type*} (μ : ι → M → V →L[ℂ] ℂ)
    (hμ : ∀ i k, MDifferentiableOn 𝓘(ℂ, E) 𝓘(ℂ, ℂ)
      (fun s => μ i s (ℓ s (Pi.single k 1))) W)
    (hsep : ∀ z, (∀ i, μ i s₀ (ℓ s₀ z) = 0) → z = 0)
    {v : M → V} {p : M → ℂ}
    (hv : ∀ s ∈ W ∩ D, v s ∈ Set.range (ℓ s))
    (htest : ∀ i, ∃ T : Set M, IsOpen T ∧ s₀ ∈ T ∧ ∃ b : M → ℂ,
      MDifferentiableOn 𝓘(ℂ, E) 𝓘(ℂ, ℂ) b T ∧
      EqOn b (fun s => p s * μ i s (v s)) (T ∩ D)) :
    ∃ O ⊆ W, IsOpen O ∧ s₀ ∈ O ∧ ∃ H : M → V,
      IsHolomorphicOn 𝓘(ℂ, E) H O ∧ EqOn H (fun s => p s • v s) (O ∩ D) := by
  classical
  let r : ι → Fin n → ℂ := fun i k => μ i s₀ (ℓ s₀ (Pi.single k 1))
  obtain ⟨a, ha⟩ := exists_det_ne_zero r (fun z hz => hsep z fun i => by
    rw [clm_apply_eq_sum_mul, ← hz i]
    simp only [r, dotProduct, mul_comm])
  let A (s : M) : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.of fun j k => μ (a j) s (ℓ s (Pi.single k 1))
  have hA : ∀ j k, MDifferentiableOn 𝓘(ℂ, E) 𝓘(ℂ, ℂ) (fun s => A s j k) W :=
    fun j k => hμ (a j) k
  have hdet := mdifferentiableOn_det hA
  choose T hT hsT b hb hbeq using fun j => htest (a j)
  let O := (W ∩ (fun s => (A s).det) ⁻¹' ({0}ᶜ : Set ℂ)) ∩ ⋂ j, T j
  have hOW : O ⊆ W := fun _ hs => hs.1.1
  have hOT (j : Fin n) : O ⊆ T j := fun _ hs => mem_iInter.mp hs.2 j
  have hO : IsOpen O :=
    (hdet.continuousOn.isOpen_inter_preimage hW isClosed_singleton.isOpen_compl).inter
      (isOpen_iInter_of_finite hT)
  have hOdet {s : M} (hs : s ∈ O) : (A s).det ≠ 0 := hs.1.2
  let B (s : M) : Fin n → ℂ := fun j => b j s
  let z (s : M) : Fin n → ℂ := (A s).det⁻¹ • ((A s).adjugate *ᵥ B s)
  have hz (k : Fin n) : MDifferentiableOn 𝓘(ℂ, E) 𝓘(ℂ, ℂ) (fun s => z s k) O := by
    have hsum := mdifferentiableOn_finset_sum
      (f := fun j s => (A s).adjugate k j * b j s) Finset.univ
      (fun j _ => ((mdifferentiableOn_adjugate hA k j).mono hOW).mul ((hb j).mono (hOT j)))
    exact ((hdet.mono hOW).inv (fun _ hs => hOdet hs)).mul hsum
  refine ⟨O, hOW, hO, ⟨⟨hs₀, ha⟩, mem_iInter.mpr hsT⟩,
    fun s => recoverFromFrameTests (ℓ s) (fun j => μ (a j) s) (B s), ?_, ?_⟩
  · intro ψ
    refine (mdifferentiableOn_finset_sum
      (f := fun k s => z s k * ψ (ℓ s (Pi.single k 1))) Finset.univ
      (fun k _ => (hz k).mul ((hℓ (Pi.single k 1) ψ).mono hOW))).congr fun s _ => ?_
    exact clm_apply_eq_sum_mul ψ (ℓ s) (z s)
  · intro s hs
    have hsWD : s ∈ W ∩ D := ⟨hOW hs.1, hs.2⟩
    obtain ⟨x, hx⟩ := hv s hsWD
    have hAx : A s *ᵥ (p s • x) = B s := by
      funext j
      have hb' : B s j = p s * μ (a j) s (v s) := hbeq j ⟨hOT j hs.1, hs.2⟩
      rw [hb', ← hx, ← smul_eq_mul, ← map_smul, ← map_smul, clm_apply_eq_sum_mul]
      simp only [A, Matrix.mulVec, Matrix.of_apply, dotProduct, mul_comm]
    have hzx : z s = p s • x := by
      simp only [z, ← hAx, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec,
        Matrix.one_mulVec, smul_smul, ← mul_assoc, inv_mul_cancel₀ (hOdet hs.1), one_mul]
    change ℓ s (z s) = p s • v s
    rw [hzx, map_smul, hx]

end Langlands.Analysis.Meromorphic
