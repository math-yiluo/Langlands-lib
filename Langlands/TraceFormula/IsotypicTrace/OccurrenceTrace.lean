import Langlands.TraceFormula.IsotypicTrace.OccurrenceHilbertSum
import Langlands.Analysis.HilbertSumTraceProof
import Langlands.Analysis.OperatorTraceFiniteCompression
import Langlands.LinearAlgebra.FiniteRankTrace

/-!
# Traces of compressions to closures of local occurrences

* On a finite-dimensional Hilbert space the operator trace is the linear-algebra trace
  (`operatorTrace_eq_linearMap_trace`).
* If the range of a trace-class operator `D` lies in the image of a finite-dimensional
  subspace `V₀` under an injective linear map `J`, and `D ∘ J = J ∘ L` on `V₀`, then the
  trace of `D` is the trace of `L` on `V₀` (`operatorTrace_eq_trace_of_range`).
* For a Hilbert sum `E = ⨁ W i` and a trace-class `B` whose compressions to the `W i` have
  traces `c i * τ`, the trace of `B` is `τ * ∑' i, c i` (`operatorTrace_eq_mul_tsum`); the sum
  need not converge when `τ = 0`.
* For the closure `W` of the range of a local occurrence `j` of an admissible representation
  and a trace-class `B` whose values are fixed by an open subgroup `K`, if
  `P_W (B (j v)) = j (L v)` for an endomorphism `L` with values in the `K`-fixed vectors,
  then the trace of the compression of `B` to `W` is the trace of `L` on the `K`-fixed vectors
  (`operatorTrace_compression_occurrence`).
-/

noncomputable section

open MeasureTheory Langlands.Analysis.OperatorIdeals

namespace Langlands.TraceFormula.IsotypicTrace

universe uG uE uV uM uι

section Finite

variable {M : Type uM} [NormedAddCommGroup M] [InnerProductSpace ℂ M] [CompleteSpace M]
  [FiniteDimensional ℂ M]

/-- On a finite-dimensional Hilbert space the operator trace is the linear-algebra trace. -/
theorem operatorTrace_eq_linearMap_trace (A : M →L[ℂ] M) :
    operatorTrace A = LinearMap.trace ℂ M A.toLinearMap := by
  let b := stdOrthonormalBasis ℂ M
  rw [operatorTrace_eq_sum_diagonal b A, LinearMap.trace_eq_matrix_trace ℂ b.toBasis,
    Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_toBasis]
  rfl

end Finite

section Range

variable {M : Type uM} [NormedAddCommGroup M] [InnerProductSpace ℂ M] [CompleteSpace M]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- A trace-class operator with range in the image `J V₀` of a finite-dimensional subspace,
acting there as `L`, has trace `tr L`. -/
theorem operatorTrace_eq_trace_of_range (D : M →L[ℂ] M) (hD : IsTraceClass D)
    (J : V →ₗ[ℂ] M) (hJ : Function.Injective J) (V₀ : Submodule ℂ V) [FiniteDimensional ℂ V₀]
    (L : Module.End ℂ V₀) (hrange : ∀ x, D x ∈ V₀.map J)
    (hact : ∀ v : V₀, D (J v) = J (L v)) :
    operatorTrace D = LinearMap.trace ℂ V₀ L := by
  let S : Submodule ℂ M := V₀.map J
  have : FiniteDimensional ℂ S := Module.Finite.map _ _
  have : CompleteSpace S := FiniteDimensional.complete ℂ S
  obtain ⟨-, htr⟩ := compression_trace_of_range S D hD hrange
  rw [← htr, operatorTrace_eq_linearMap_trace]
  let e : V₀ ≃ₗ[ℂ] S := Submodule.equivMapOfInjective J hJ V₀
  have hconj : (S.orthogonalProjectionOnto ∘L D ∘L S.subtypeL).toLinearMap = e.conj L := by
    apply LinearMap.ext
    intro s
    obtain ⟨v, rfl⟩ := e.surjective s
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
    apply Subtype.ext
    have h1 : ((e v : S) : M) = J v := rfl
    have h2 : ((e (L v) : S) : M) = J (L v) := rfl
    change ((S.orthogonalProjectionOnto (D ((e v : S) : M)) : S) : M) = ((e (L v) : S) : M)
    rw [h1, h2, hact v]
    have hmem : J (L v) ∈ S := ⟨L v, (L v).property, rfl⟩
    exact congrArg Subtype.val
      (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (K := S) ⟨J (L v), hmem⟩)
  rw [hconj, LinearMap.trace_conj']

end Range

section HilbertSum

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- If the compressions of a trace-class operator to the summands of a Hilbert sum have traces
`c i * τ`, its trace is `τ * ∑' i, c i`. -/
theorem operatorTrace_eq_mul_tsum {ι : Type uι} (W : ι → Submodule ℂ E)
    [∀ i, CompleteSpace (W i)]
    (hW : IsHilbertSum ℂ (fun i => W i) (fun i => (W i).subtypeₗᵢ))
    (B : E →L[ℂ] E) (hB : IsTraceClass B) (c : ι → ℂ) (τ : ℂ)
    (h : ∀ i, operatorTrace ((W i).orthogonalProjectionOnto ∘L B ∘L (W i).subtypeL) =
      c i * τ) :
    operatorTrace B = τ * ∑' i, c i := by
  have hs := (hilbertSum_trace_hasSum W hW B hB).2
  simp_rw [h] at hs
  by_cases hτ : τ = 0
  · subst hτ
    simp only [mul_zero] at hs
    rw [hs.unique hasSum_zero, zero_mul]
  · have hc : HasSum c (operatorTrace B / τ) := by
      have := hs.mul_right τ⁻¹
      simpa [mul_assoc, mul_inv_cancel₀ hτ, div_eq_mul_inv] using this
    rw [hc.tsum_eq]
    field_simp

end HilbertSum

section Occurrence

variable {Gv : Type uG} [Group Gv] [TopologicalSpace Gv] [IsTopologicalGroup Gv]
  [MeasurableSpace Gv] [BorelSpace Gv] [T2Space Gv] [LocallyCompactSpace Gv]
  [TotallyDisconnectedSpace Gv] [SecondCountableTopology Gv]
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (σ : Gv →* (E →L[ℂ] E))
variable {V : Type uV} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ Gv V)

omit [TopologicalSpace Gv] [IsTopologicalGroup Gv] [MeasurableSpace Gv] [BorelSpace Gv]
  [T2Space Gv] [LocallyCompactSpace Gv] [TotallyDisconnectedSpace Gv]
  [SecondCountableTopology Gv] in
/-- The orthogonal projection onto the closure of a local occurrence commutes with the local
action. -/
theorem starProjection_closureRange_commute
    (hσinner : ∀ y x x', inner ℂ (σ y x) (σ y x') = inner ℂ x x')
    (j : V →ₗ[ℂ] E) (hj : ∀ y x, j (ρ y x) = σ y (j x))
    [((LinearMap.range j).topologicalClosure).HasOrthogonalProjection] (y : Gv) (x : E) :
    ((LinearMap.range j).topologicalClosure).starProjection (σ y x) =
      σ y (((LinearMap.range j).topologicalClosure).starProjection x) :=
  starProjection_commute σ hσinner _ y
    (closureRange_invariant σ ρ (MonoidHom.id Gv) j hj y)
    (closureRange_invariant σ ρ (MonoidHom.id Gv) j hj y⁻¹) x

/-- **Trace of the compression to the closure of a local occurrence.** -/
theorem operatorTrace_compression_occurrence (μ : Measure Gv) [μ.IsHaarMeasure]
    (hσinner : ∀ y x x', inner ℂ (σ y x) (σ y x') = inner ℂ x x')
    (hσnorm : ∀ y x, ‖σ y x‖ = ‖x‖) (hσcont : ∀ x, Continuous fun y => σ y x)
    (hρ : IsAdmissible ρ) (j : V →ₗ[ℂ] E) (hj : ∀ y x, j (ρ y x) = σ y (j x))
    (hinj : Function.Injective j)
    [CompleteSpace ((LinearMap.range j).topologicalClosure)]
    (K : OpenSubgroup Gv) (B : E →L[ℂ] E) (hB : IsTraceClass B)
    (hBK : ∀ x, ∀ k ∈ K, σ k (B x) = B x)
    (L : Module.End ℂ V) (hLK : LinearMap.range L ≤ fixedVectors ρ K.toSubgroup)
    (hBL : ∀ v, ((LinearMap.range j).topologicalClosure).starProjection (B (j v)) = j (L v)) :
    letI := hρ.2 K
    operatorTrace (((LinearMap.range j).topologicalClosure).orthogonalProjectionOnto ∘L B ∘L
        ((LinearMap.range j).topologicalClosure).subtypeL) =
      LinearMap.trace ℂ (fixedVectors ρ K.toSubgroup)
        (FiniteRankEnd.onSubspace L (fixedVectors ρ K.toSubgroup) hLK) := by
  let W : Submodule ℂ E := (LinearMap.range j).topologicalClosure
  have : Module.Finite ℂ (fixedVectors ρ K.toSubgroup) := hρ.2 K
  let J : V →ₗ[ℂ] W := j.codRestrict W fun v => (LinearMap.range j).le_topologicalClosure ⟨v, rfl⟩
  have hJ : Function.Injective J := fun a b h => hinj (congrArg Subtype.val h)
  have hJv : ∀ v, (J v : E) = j v := fun v => rfl
  apply operatorTrace_eq_trace_of_range _ (isTraceClass_compression W B hB) J hJ
  · intro w
    have hfixed : ∀ k ∈ K, σ k (W.starProjection (B w)) = W.starProjection (B w) := by
      intro k hk
      rw [← starProjection_closureRange_commute σ ρ hσinner j hj, hBK w k hk]
    obtain ⟨v, hv, hjv⟩ := exists_fixed_preimage_of_mem_closure σ ρ μ hσnorm hσcont hρ j hj
      hinj K (W.starProjection (B w)) (W.starProjection_apply_mem _) hfixed
    refine ⟨v, hv, Subtype.ext ?_⟩
    rw [hJv, hjv, Submodule.starProjection_apply]
    rfl
  · intro v
    apply Subtype.ext
    change ((W.orthogonalProjectionOnto (B (J v)) : W) : E) = J (L v)
    rw [hJv, hJv, ← Submodule.starProjection_apply, hBL]

end Occurrence

end Langlands.TraceFormula.IsotypicTrace
