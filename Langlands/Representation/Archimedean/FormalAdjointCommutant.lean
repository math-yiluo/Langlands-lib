import Langlands.Representation.Archimedean.UnitaryCommutant
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Operators with a formal adjoint commuting with an irreducible unitary action

Let `ρ` be a topologically irreducible unitary representation of a group on a complex Hilbert
space `E`, and `W` a nonzero `ρ`-invariant subspace. A linear operator `D : W → W` which has a
formal adjoint `D' : W → W` (`⟪D v, w⟫ = ⟪v, D' w⟫`) and commutes with `ρ` on `W` is a scalar.
This is the form of Schur's lemma used, after Segal, to show that the center of the enveloping
algebra acts by scalars on the smooth vectors of an irreducible unitary representation.

The proof uses bounded operators only. For a symmetric `S`, the operator `S - i` satisfies
`‖(S - i) w‖ ≥ ‖w‖`; its range is invariant and nonzero, hence dense; the inverse `(S - i)⁻¹`
extends to a contraction of `E` commuting with `ρ`, which is a scalar by
`exists_eq_scalar_of_unitary_commute`. A general `D` is a combination of the symmetric
operators `D + D'` and `i (D - D')`.
-/

noncomputable section

open scoped InnerProductSpace

namespace Langlands.Archimedean.FormalAdjointCommutant

variable {G E : Type*} [Group G] [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A nonzero invariant subspace of a topologically irreducible representation is dense. -/
theorem dense_of_invariant (ρ : G →* (E →L[ℂ] E)) (hirr : IsTopologicallyIrreducible ρ)
    (W : Submodule ℂ E) (hW : ∀ g, ∀ w ∈ W, ρ g w ∈ W) (hne : W ≠ ⊥) :
    Dense (W : Set E) := by
  have hinv : ∀ (g : G), ∀ w ∈ W.topologicalClosure, ρ g w ∈ W.topologicalClosure := by
    intro g w hw
    exact map_mem_closure (ρ g).continuous hw (fun x hx => hW g x hx)
  rcases hirr.2 W.topologicalClosure W.isClosed_topologicalClosure hinv with h | h
  · exact absurd (le_bot_iff.mp (h ▸ W.le_topologicalClosure)) hne
  · exact Submodule.dense_iff_topologicalClosure_eq_top.mpr h

/-- Vectors with the same inner products against a dense set are equal. -/
theorem eq_of_inner_dense {W : Submodule ℂ E} (hd : Dense (W : Set E)) {x y : E}
    (h : ∀ w ∈ W, ⟪w, x⟫_ℂ = ⟪w, y⟫_ℂ) : x = y := by
  have hcl : IsClosed {v : E | ⟪v, x - y⟫_ℂ = 0} :=
    isClosed_eq (continuous_id.inner continuous_const) continuous_const
  have hsub : (W : Set E) ⊆ {v : E | ⟪v, x - y⟫_ℂ = 0} := by
    intro w hw
    simp [inner_sub_right, h w hw]
  have hz : ⟪x - y, x - y⟫_ℂ = 0 := (hcl.closure_subset_iff.mpr hsub) (hd (x - y))
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hz)

/-- The adjoint of a unitary operator `ρ g` moves to the other side as `ρ g⁻¹`. -/
theorem inner_map_right (ρ : G →* (E →L[ℂ] E))
    (hunit : ∀ g v w, ⟪ρ g v, ρ g w⟫_ℂ = ⟪v, w⟫_ℂ) (g : G) (x y : E) :
    ⟪x, ρ g y⟫_ℂ = ⟪ρ g⁻¹ x, y⟫_ℂ := by
  rw [← hunit g (ρ g⁻¹ x) y]
  congr 1
  change x = (ρ g * ρ g⁻¹) x
  rw [← map_mul, mul_inv_cancel, map_one]
  rfl

variable [CompleteSpace E]

/-- **Symmetric case.** A symmetric operator on a nonzero invariant subspace commuting with a
topologically irreducible unitary representation is a scalar. -/
theorem exists_eq_smul_of_symmetric_commute (ρ : G →* (E →L[ℂ] E))
    (hunit : ∀ g v w, ⟪ρ g v, ρ g w⟫_ℂ = ⟪v, w⟫_ℂ) (hirr : IsTopologicallyIrreducible ρ)
    (W : Submodule ℂ E) (hW : ∀ g, ∀ w ∈ W, ρ g w ∈ W) (hne : W ≠ ⊥)
    (S : W →ₗ[ℂ] W) (hS : ∀ v w : W, ⟪(S v : E), w⟫_ℂ = ⟪(v : E), S w⟫_ℂ)
    (hcomm : ∀ (g : G) (w : W), (S ⟨ρ g w, hW g w w.2⟩ : E) = ρ g (S w)) :
    ∃ c : ℂ, ∀ w : W, (S w : E) = c • (w : E) := by
  let T : W →ₗ[ℂ] E := W.subtype ∘ₗ (S - Complex.I • LinearMap.id)
  have hTapply (w : W) : T w = (S w : E) - Complex.I • (w : E) := rfl
  -- `‖(S - i) w‖ ≥ ‖w‖`
  have hT (w : W) : ‖(w : E)‖ ≤ ‖T w‖ := by
    have hre : RCLike.re ⟪(S w : E), Complex.I • (w : E)⟫_ℂ = 0 := by
      rw [inner_smul_right]
      have him : (⟪(S w : E), (w : E)⟫_ℂ).im = 0 := by
        have h1 : ⟪(S w : E), (w : E)⟫_ℂ = (starRingEnd ℂ) ⟪(S w : E), (w : E)⟫_ℂ := by
          rw [inner_conj_symm]
          exact hS w w
        have h2 := congrArg Complex.im h1
        rw [Complex.conj_im] at h2
        linarith
      simp [him]
    have hsq : ‖T w‖ ^ 2 = ‖(S w : E)‖ ^ 2 + ‖(w : E)‖ ^ 2 := by
      rw [hTapply, @norm_sub_sq ℂ, hre, norm_smul, Complex.norm_I, one_mul]
      ring
    have hle : ‖(w : E)‖ ^ 2 ≤ ‖T w‖ ^ 2 := by
      rw [hsq]
      nlinarith [sq_nonneg ‖(S w : E)‖]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hle
  -- the range of `S - i` is dense
  have hTcomm (g : G) (w : W) : T ⟨ρ g w, hW g w w.2⟩ = ρ g (T w) := by
    rw [hTapply, hTapply, hcomm, map_sub, map_smul]
  have hdense : DenseRange T := by
    have hM : Dense (LinearMap.range T : Set E) := by
      apply dense_of_invariant ρ hirr
      · rintro g _ ⟨w, rfl⟩
        exact ⟨⟨ρ g w, hW g w w.2⟩, hTcomm g w⟩
      · obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff W).mp hne
        rw [Submodule.ne_bot_iff]
        refine ⟨T ⟨w, hw⟩, LinearMap.mem_range_self T _, fun h0 => hw0 ?_⟩
        have := hT ⟨w, hw⟩
        rw [h0, norm_zero] at this
        exact norm_le_zero_iff.mp this
    rw [DenseRange, ← LinearMap.coe_range]
    exact hM
  -- the inverse of `S - i` extends to a bounded operator commuting with `ρ`
  have hbound : ∃ C, ∀ x : W, ‖W.subtype x‖ ≤ C * ‖T x‖ :=
    ⟨1, fun x => by simpa using hT x⟩
  let R : E →L[ℂ] E := W.subtype.extendOfNorm T
  have hR (w : W) : R (T w) = w := LinearMap.extendOfNorm_eq hdense hbound w
  have hRc : ∀ g, Commute R (ρ g) := by
    intro g
    apply ContinuousLinearMap.ext
    intro x
    have hfun : (fun x => R (ρ g x)) = (fun x => ρ g (R x)) := by
      apply hdense.equalizer (R.continuous.comp (ρ g).continuous)
        ((ρ g).continuous.comp R.continuous)
      funext w
      simp only [Function.comp_apply]
      rw [← hTcomm, hR, hR]
    exact congrFun hfun x
  obtain ⟨c, hc⟩ := exists_eq_scalar_of_unitary_commute ρ hunit hirr R hRc
  have hcw (w : W) : (w : E) = c • T w := by
    rw [← hR w, hc]
    rfl
  have hc0 : c ≠ 0 := by
    intro h0
    obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff W).mp hne
    have := hcw ⟨w, hw⟩
    rw [h0, zero_smul] at this
    exact hw0 this
  refine ⟨c⁻¹ + Complex.I, fun w => ?_⟩
  have h1 : T w = c⁻¹ • (w : E) := by
    rw [hcw w, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  rw [hTapply] at h1
  rw [add_smul, ← h1, sub_add_cancel]

/-- **Schur's lemma with a formal adjoint.** Let `ρ` be a topologically irreducible unitary
representation on a complex Hilbert space `E` and `W` a nonzero `ρ`-invariant subspace. A linear
operator `D : W → W` with a formal adjoint `D' : W → W`, i.e. `⟪D v, w⟫ = ⟪v, D' w⟫` for
`v, w ∈ W`, which commutes with every `ρ g` on `W`, is a scalar on `W`. -/
theorem exists_eq_smul_of_formalAdjoint_commute (ρ : G →* (E →L[ℂ] E))
    (hunit : ∀ g v w, ⟪ρ g v, ρ g w⟫_ℂ = ⟪v, w⟫_ℂ) (hirr : IsTopologicallyIrreducible ρ)
    (W : Submodule ℂ E) (hW : ∀ g, ∀ w ∈ W, ρ g w ∈ W) (hne : W ≠ ⊥)
    (D D' : W →ₗ[ℂ] W) (hadj : ∀ v w : W, ⟪(D v : E), w⟫_ℂ = ⟪(v : E), D' w⟫_ℂ)
    (hcomm : ∀ (g : G) (w : W), (D ⟨ρ g w, hW g w w.2⟩ : E) = ρ g (D w)) :
    ∃ c : ℂ, ∀ w : W, (D w : E) = c • (w : E) := by
  have hd := dense_of_invariant ρ hirr W hW hne
  -- the reversed adjoint relation
  have hadj' (v w : W) : ⟪(D' v : E), w⟫_ℂ = ⟪(v : E), D w⟫_ℂ := by
    rw [← inner_conj_symm, ← hadj w v, inner_conj_symm]
  -- the formal adjoint also commutes with `ρ`
  have hcomm' (g : G) (w : W) : (D' ⟨ρ g w, hW g w w.2⟩ : E) = ρ g (D' w) := by
    apply eq_of_inner_dense hd
    intro x hx
    rw [← hadj ⟨x, hx⟩, inner_map_right ρ hunit, inner_map_right ρ hunit]
    have hx' : ρ g⁻¹ x ∈ W := hW g⁻¹ x hx
    have h1 := hcomm g⁻¹ ⟨x, hx⟩
    rw [← h1]
    exact hadj ⟨ρ g⁻¹ x, hx'⟩ w
  -- the two symmetric parts
  let S₁ : W →ₗ[ℂ] W := D + D'
  let S₂ : W →ₗ[ℂ] W := Complex.I • (D - D')
  have hS₁ : ∀ v w : W, ⟪(S₁ v : E), w⟫_ℂ = ⟪(v : E), S₁ w⟫_ℂ := by
    intro v w
    simp only [S₁, LinearMap.add_apply, Submodule.coe_add, inner_add_left, inner_add_right,
      hadj, hadj']
    ring
  have hS₂ : ∀ v w : W, ⟪(S₂ v : E), w⟫_ℂ = ⟪(v : E), S₂ w⟫_ℂ := by
    intro v w
    simp only [S₂, LinearMap.smul_apply, LinearMap.sub_apply, Submodule.coe_smul,
      Submodule.coe_sub, inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right,
      hadj, hadj', Complex.conj_I]
    ring
  have hc₁ : ∀ (g : G) (w : W), (S₁ ⟨ρ g w, hW g w w.2⟩ : E) = ρ g (S₁ w) := by
    intro g w
    simp only [S₁, LinearMap.add_apply, Submodule.coe_add, hcomm, hcomm', map_add]
  have hc₂ : ∀ (g : G) (w : W), (S₂ ⟨ρ g w, hW g w w.2⟩ : E) = ρ g (S₂ w) := by
    intro g w
    simp only [S₂, LinearMap.smul_apply, LinearMap.sub_apply, Submodule.coe_smul,
      Submodule.coe_sub, hcomm, hcomm', map_sub, map_smul]
  obtain ⟨a, ha⟩ := exists_eq_smul_of_symmetric_commute ρ hunit hirr W hW hne S₁ hS₁ hc₁
  obtain ⟨b, hb⟩ := exists_eq_smul_of_symmetric_commute ρ hunit hirr W hW hne S₂ hS₂ hc₂
  refine ⟨(a - Complex.I * b) / 2, fun w => ?_⟩
  have h1 := ha w
  have h2 := hb w
  simp only [S₁, S₂, LinearMap.add_apply, Submodule.coe_add, LinearMap.smul_apply,
    LinearMap.sub_apply, Submodule.coe_smul, Submodule.coe_sub] at h1 h2
  have h3 : (2 : ℂ) • (D w : E) = (a - Complex.I * b) • (w : E) := by
    rw [sub_smul, mul_smul, ← h1, ← h2, smul_smul, Complex.I_mul_I]
    module
  calc (D w : E) = (1 / 2 : ℂ) • ((2 : ℂ) • (D w : E)) := by
        rw [smul_smul]; norm_num
    _ = ((a - Complex.I * b) / 2) • (w : E) := by
        rw [h3, smul_smul]; ring_nf

end Langlands.Archimedean.FormalAdjointCommutant
