import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic.NoncommRing

/-! # Square roots near one in finite-dimensional algebras over complete fields -/

noncomputable section

namespace Langlands.CentralSimple.Landherr

open scoped NNReal
open Set Filter Topology

section Normed

variable {k A : Type*} [NontriviallyNormedField k] [CompleteSpace k] [NormedRing A]
  [NormedAlgebra k A] [CompleteSpace A] [FiniteDimensional k A]

omit [CompleteSpace k] [CompleteSpace A] [FiniteDimensional k A] in
private theorem commute_of_mem_adjoin {b s s' : A} (hs : s ∈ Algebra.adjoin k {b})
    (hs' : s' ∈ Algebra.adjoin k {b}) : Commute s s' :=
  Algebra.commute_of_mem_adjoin_singleton_of_commute hs'
    (Algebra.commute_of_mem_adjoin_self hs).symm

/-- In a complete finite-dimensional normed algebra over a complete field in which `2 ≠ 0`,
every element close enough to `1` is the square of an element of the subalgebra it
generates. The neighbourhood depends only on the norm of `2⁻¹`. -/
theorem exists_mul_self_eq_of_norm_sub_one_lt (h2 : (2 : k) ≠ 0) :
    ∃ δ > (0 : ℝ), ∀ b : A, ‖b - 1‖ < δ → ∃ s ∈ Algebra.adjoin k {b}, s * s = b := by
  set c : ℝ := ‖(2 : k)⁻¹‖ with hc
  have hc0 : 0 < c := norm_pos_iff.mpr (inv_ne_zero h2)
  set ρ : ℝ := 1 / (4 * c) with hρ
  have hρ0 : 0 < ρ := by positivity
  have hcρ : c * ρ = 1 / 4 := by rw [hρ]; field_simp
  refine ⟨ρ / (2 * c), by positivity, fun b hb => ?_⟩
  set C : Subalgebra k A := Algebra.adjoin k {b}
  set T : Set A := {s | s ∈ C ∧ ‖s - 1‖ ≤ ρ} with hT
  set φ : A → A := fun s => s + (2 : k)⁻¹ • (b - s * s) with hφ
  have h2inv : (2 : k)⁻¹ • (2 : A) = 1 := by
    rw [show (2 : A) = (2 : k) • (1 : A) by rw [two_smul, one_add_one_eq_two], smul_smul,
      inv_mul_cancel₀ h2, one_smul]
  have hφ1 : ∀ s, φ s - 1 = (2 : k)⁻¹ • ((b - 1) - (s - 1) * (s - 1)) := by
    intro s
    have : (b - 1) - (s - 1) * (s - 1) = (b - s * s) + (2 : A) * (s - 1) := by noncomm_ring
    show s + (2 : k)⁻¹ • (b - s * s) - 1 = _
    rw [this, smul_add, ← smul_mul_assoc, h2inv, one_mul]
    abel
  have hmaps : MapsTo φ T T := by
    rintro s ⟨hsC, hs1⟩
    refine ⟨C.add_mem hsC (C.smul_mem (C.sub_mem (Algebra.self_mem_adjoin_singleton k b)
      (C.mul_mem hsC hsC)) _), ?_⟩
    rw [hφ1, norm_smul]
    calc c * ‖(b - 1) - (s - 1) * (s - 1)‖ ≤ c * (‖b - 1‖ + ‖s - 1‖ * ‖s - 1‖) := by
          gcongr
          exact (norm_sub_le _ _).trans (by gcongr; exact norm_mul_le _ _)
      _ ≤ c * (ρ / (2 * c) + ρ * ρ) := by gcongr
      _ = ρ / 2 + (c * ρ) * ρ := by field_simp
      _ ≤ ρ := by rw [hcρ]; linarith
  have hlip : ∀ s ∈ T, ∀ s' ∈ T, ‖φ s - φ s'‖ ≤ (1 / 2) * ‖s - s'‖ := by
    rintro s ⟨hsC, hs1⟩ s' ⟨hs'C, hs'1⟩
    have hcomm := commute_of_mem_adjoin hsC hs'C
    have e : (s - s') * ((1 - s) + (1 - s')) = (2 : A) * (s - s') - (s * s - s' * s') := by
      have h := hcomm.eq
      rw [← sub_eq_zero]
      calc _ = s' * s - s * s' := by noncomm_ring
        _ = 0 := by rw [h, sub_self]
    have : φ s - φ s' = (s - s') * ((2 : k)⁻¹ • ((1 - s) + (1 - s'))) := by
      calc φ s - φ s' = (s - s') - (2 : k)⁻¹ • (s * s - s' * s') := by
            show s + (2 : k)⁻¹ • (b - s * s) - (s' + (2 : k)⁻¹ • (b - s' * s')) = _
            rw [smul_sub, smul_sub, smul_sub]
            abel
        _ = (2 : k)⁻¹ • ((2 : A) * (s - s')) - (2 : k)⁻¹ • (s * s - s' * s') := by
            rw [← smul_mul_assoc, h2inv, one_mul]
        _ = (2 : k)⁻¹ • ((s - s') * ((1 - s) + (1 - s'))) := by rw [e, ← smul_sub]
        _ = (s - s') * ((2 : k)⁻¹ • ((1 - s) + (1 - s'))) := by rw [mul_smul_comm]
    rw [this]
    calc ‖(s - s') * ((2 : k)⁻¹ • ((1 - s) + (1 - s')))‖
        ≤ ‖s - s'‖ * (c * (ρ + ρ)) := by
          refine (norm_mul_le _ _).trans ?_
          gcongr
          rw [norm_smul]
          gcongr
          refine (norm_add_le _ _).trans ?_
          rw [norm_sub_rev 1 s, norm_sub_rev 1 s']
          gcongr
      _ = (1 / 2) * ‖s - s'‖ := by rw [mul_add, hcρ]; ring
  have hcomplete : IsComplete T := by
    apply IsClosed.isComplete
    have hCcl : IsClosed (C : Set A) :=
      Submodule.closed_of_finiteDimensional (Subalgebra.toSubmodule C)
    exact hCcl.inter (isClosed_le (continuous_id.sub continuous_const).norm continuous_const)
  have hcontr : ContractingWith (1 / 2 : ℝ≥0) (hmaps.restrict φ T T) := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    simp only [MapsTo.val_restrict_apply, Subtype.dist_eq, dist_eq_norm]
    simpa using hlip x x.2 y y.2
  have h1T : (1 : A) ∈ T := ⟨C.one_mem, by simpa using hρ0.le⟩
  obtain ⟨s, hsT, hfix, -⟩ := ContractingWith.exists_fixedPoint' hcomplete hmaps hcontr h1T
    (edist_ne_top _ _)
  refine ⟨s, hsT.1, ?_⟩
  have : (2 : k)⁻¹ • (b - s * s) = 0 := by
    have h := hfix.eq
    rw [hφ] at h
    simpa using h
  rw [smul_eq_zero] at this
  rcases this with h | h
  · exact absurd h (inv_ne_zero h2)
  · exact (sub_eq_zero.mp h).symm

end Normed

section Coordinates

variable {k A : Type*} [NontriviallyNormedField k] [CompleteSpace k] [Ring A] [Algebra k A]
  [FiniteDimensional k A] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The left regular representation of `A` on the coordinate space of a basis, with values in
continuous linear maps. -/
def coordinateLeftMul (b : Module.Basis ι k A) : A →ₐ[k] ((ι → k) →L[k] (ι → k)) :=
  AlgHom.ofLinearMap
    (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ
      (LinearEquiv.conj b.equivFun).toLinearMap ∘ₗ (Algebra.lmul k A).toLinearMap)
    (by ext x i; simp [LinearEquiv.conj_apply, Finsupp.single_apply])
    (by intro x y; ext z i; simp [LinearEquiv.conj_apply, mul_assoc])

theorem coordinateLeftMul_injective (b : Module.Basis ι k A) :
    Function.Injective (coordinateLeftMul b) := by
  intro x y h
  have := congrArg (fun f => b.equivFun.symm (f (b.equivFun 1))) h
  simpa [coordinateLeftMul, LinearEquiv.conj_apply] using this

/-- In a finite-dimensional algebra over a complete nontrivially normed field `k`
with `2 ≠ 0`, there is an open set containing the coordinates of `1`. Every element
whose coordinates lie in this set is a square in the `k`-subalgebra it generates. -/
theorem exists_isOpen_mul_self_eq (b : Module.Basis ι k A) (h2 : (2 : k) ≠ 0) :
    ∃ U : Set (ι → k), IsOpen U ∧ b.equivFun 1 ∈ U ∧
      ∀ a : A, b.equivFun a ∈ U → ∃ s ∈ Algebra.adjoin k {a}, s * s = a := by
  obtain ⟨δ, hδ, hsq⟩ := exists_mul_self_eq_of_norm_sub_one_lt
    (A := (ι → k) →L[k] (ι → k)) h2
  set L := coordinateLeftMul b
  let f : (ι → k) →ₗ[k] ((ι → k) →L[k] (ι → k)) :=
    L.toLinearMap ∘ₗ b.equivFun.symm.toLinearMap
  have hf : Continuous f := f.continuous_of_finiteDimensional
  refine ⟨f ⁻¹' Metric.ball 1 δ, Metric.isOpen_ball.preimage hf, ?_, fun a ha => ?_⟩
  · simp [f, L, hδ]
  · have ha' : ‖L a - 1‖ < δ := by simpa [f, dist_eq_norm] using ha
    obtain ⟨S, hS, hSS⟩ := hsq (L a) ha'
    rw [← AlgHom.map_adjoin_singleton] at hS
    obtain ⟨s, hs, rfl⟩ := hS
    refine ⟨s, hs, coordinateLeftMul_injective b ?_⟩
    rw [map_mul]
    exact hSS

end Coordinates

end Langlands.CentralSimple.Landherr
