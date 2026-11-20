import Langlands.LinearAlgebra.CyclicMatrixTranspose
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Normed.Module.RCLike.Real

/-! # Cyclic directions and centralizer orbit closure -/

noncomputable section

open Filter Matrix Polynomial Set
open scoped Topology

set_option autoImplicit false

namespace Langlands

variable {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/-- The determinant of the cyclic-vector columns over the polynomial ring along
the line `A + t • D`. -/
def cyclicVectorLinePolynomial (A D : Mat) (v : Fin n → ℝ) : ℝ[X] :=
  let M := A.map Polynomial.C + (Polynomial.X : ℝ[X]) • D.map Polynomial.C
  (Matrix.of fun i j : Fin n => (M ^ (j : ℕ) *ᵥ (Polynomial.C ∘ v)) i).det

/-- Evaluation on the line parameter commutes with forming the cyclic-vector determinant. -/
theorem eval_cyclicVectorLinePolynomial (A D : Mat) (v : Fin n → ℝ) (t : ℝ) :
    (cyclicVectorLinePolynomial A D v).eval t = (cyclicVectorMatrix (A + t • D) v).det := by
  let f := Polynomial.evalRingHom t
  let M := A.map Polynomial.C + (Polynomial.X : ℝ[X]) • D.map Polynomial.C
  have hM : M.map f = A + t • D := by
    ext i j
    change (Polynomial.C (A i j) + Polynomial.X * Polynomial.C (D i j)).eval t =
      A i j + t * D i j
    rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C,
      Polynomial.eval_C]
  have hv : f ∘ (Polynomial.C ∘ v) = v := funext fun i => Polynomial.eval_C
  change f (Matrix.of fun i j : Fin n => (M ^ (j : ℕ) *ᵥ (Polynomial.C ∘ v)) i).det = _
  rw [RingHom.map_det]
  congr 1
  ext i j
  change f ((M ^ (j : ℕ) *ᵥ (Polynomial.C ∘ v)) i) = _
  rw [RingHom.map_mulVec, hv]
  change (((f.mapMatrix (m := Fin n)) (M ^ (j : ℕ))) *ᵥ v) i =
    ((A + t • D) ^ (j : ℕ) *ᵥ v) i
  rw [map_pow]
  change ((M.map f ^ (j : ℕ)) *ᵥ v) i = _
  rw [hM]

/-- If one endpoint has a cyclic vector, the affine line is cyclic sufficiently close
to the other endpoint, with that endpoint itself excluded. -/
theorem eventually_hasCyclicMatrixVector_line (A D : Mat) (h : HasCyclicMatrixVector (A + D)) :
    ∀ᶠ t : ℝ in 𝓝[≠] 0, HasCyclicMatrixVector (A + t • D) := by
  obtain ⟨v, hv⟩ := h
  let p := cyclicVectorLinePolynomial A D v
  have h₁ : p.eval 1 ≠ 0 := by
    rw [eval_cyclicVectorLinePolynomial, one_smul]
    exact hv
  have hp : p ≠ 0 := by
    intro hzero
    exact h₁ (by simp [hzero])
  let rootsAway := {t : ℝ | IsRoot p t} \ {0}
  have hclosed : IsClosed rootsAway := ((finite_setOfPred_isRoot hp).sdiff (t := {0})).isClosed
  have hzero : (0 : ℝ) ∈ rootsAwayᶜ := by simp [rootsAway]
  have hnear : ∀ᶠ t : ℝ in 𝓝[≠] 0, t ∈ rootsAwayᶜ :=
    nhdsWithin_le_nhds (hclosed.isOpen_compl.mem_nhds hzero)
  filter_upwards [hnear, self_mem_nhdsWithin] with t ht ht₀
  refine ⟨v, ?_⟩
  rw [← eval_cyclicVectorLinePolynomial]
  exact fun hz => ht ⟨hz, ht₀⟩

/-- The adjusted transpose of a commuting matrix is approximated by conjugates of nearby
points of a prescribed affine line, using conjugators in the fixed matrix's centralizer.
The cyclicity hypothesis allows a shift by the fixed matrix itself. -/
theorem mem_closure_centralizerConjugacy_adjustedTranspose {C A D : Mat} {q : Matˣ}
    (hq : q.val * C * q.inv = Cᵀ) (hA : Commute C A) (hD : Commute C D)
    (hcyc : HasCyclicMatrixVector (A + C + D)) {S : Set Mat}
    (hS : ∀ t : ℝ, A + t • D ∈ S) :
    (A, q.inv * Aᵀ * q.val) ∈ closure {p : Mat × Mat | p.1 ∈ S ∧
      ∃ b : Matˣ, Commute (b : Mat) C ∧ b.val * p.1 * b.inv = p.2} := by
  let L : ℝ → Mat := fun t => A + t • D
  let σ : Mat → Mat := fun X => q.inv * Xᵀ * q.val
  have hL : Continuous L := continuous_const.add (continuous_id.smul continuous_const)
  have hσ : Continuous σ :=
    (continuous_const.mul continuous_id.matrix_transpose).mul continuous_const
  have hlim : Tendsto (fun t => (L t, σ (L t))) (𝓝[≠] 0) (𝓝 (A, σ A)) := by
    have h := (hL.prodMk (hσ.comp hL)).continuousAt (x := (0 : ℝ))
    simpa [L] using h.tendsto.mono_left nhdsWithin_le_nhds
  apply mem_closure_of_tendsto hlim
  filter_upwards [eventually_hasCyclicMatrixVector_line (A + C) D hcyc] with t ht
  have hcyc' : HasCyclicMatrixVector (L t + C) := by
    simpa only [L, add_right_comm A C] using ht
  have hLC : Commute C (L t + C) :=
    (hA.add_right (hD.smul_right t)).add_right (Commute.refl C)
  obtain ⟨a, ha, haC⟩ := exists_simultaneous_transpose_conjugator_of_cyclic hcyc' hLC
  let b := q⁻¹ * a
  have hb (X : Mat) : b.val * X * b.inv = q.inv * (a.val * X * a.inv) * q.val := by
    simp [b, mul_assoc]
  have hσC : σ C = C := by
    simp [σ, ← hq, mul_assoc]
  have hbC : b.val * C * b.inv = C := by rw [hb, haC]; exact hσC
  have hbc : Commute (b : Mat) C := by
    calc
      b.val * C = (b.val * C * b.inv) * b.val := by
        rw [mul_assoc (b.val * C), b.inv_val, mul_one]
      _ = C * b.val := congrArg (· * b.val) hbC
  refine ⟨hS t, b, hbc, ?_⟩
  have hsum : b.val * (L t + C) * b.inv = σ (L t + C) := by
    rw [hb, ha]
  have hadd := hsum
  simp only [σ, transpose_add, mul_add, add_mul] at hadd
  change b.val * L t * b.inv + b.val * C * b.inv = σ (L t) + σ C at hadd
  exact add_right_cancel (by rwa [hbC, hσC] at hadd)

/-- A continuous centralizer-invariant function takes equal values on a matrix and its
adjusted transpose if the prescribed line admits a cyclic witness after the shift. -/
theorem eq_adjustedTranspose_of_invariant_of_cyclic_line {Y : Type*}
    [TopologicalSpace Y] [T2Space Y] {f : Mat → Y} (hf : Continuous f)
    {C A D : Mat} {q : Matˣ} (hq : q.val * C * q.inv = Cᵀ)
    (hA : Commute C A) (hD : Commute C D)
    (hcyc : HasCyclicMatrixVector (A + C + D)) {S : Set Mat}
    (hS : ∀ t : ℝ, A + t • D ∈ S)
    (hinv : ∀ (b : Matˣ) (X : Mat), Commute (b : Mat) C → X ∈ S →
      f (b.val * X * b.inv) = f X) :
    f (q.inv * Aᵀ * q.val) = f A := by
  have hclosed : IsClosed {p : Mat × Mat | f p.2 = f p.1} :=
    isClosed_eq (hf.comp continuous_snd) (hf.comp continuous_fst)
  refine closure_minimal ?_ hclosed
    (mem_closure_centralizerConjugacy_adjustedTranspose hq hA hD hcyc hS)
  rintro p ⟨hp, b, hb, hbp⟩
  change f p.2 = f p.1
  rw [← hbp]
  exact hinv b p.1 hb hp

end Langlands
