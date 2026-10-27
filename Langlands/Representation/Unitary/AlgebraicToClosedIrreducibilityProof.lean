import Langlands.Representation.Unitary.AlgebraicToClosedIrreducibilityStatement
import Langlands.Representation.Unitary.SmoothVectorRecoveryProof
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-! # Algebraic-to-closed irreducibility in an admissible Hilbert realization -/

noncomputable section

namespace Langlands

universe uG uV uH

/-- A dense Hilbert realization of an admissible algebraically irreducible
representation, preserving its invariant positive form, is topologically
irreducible. -/
theorem admissibleAlgebraicToClosedIrreducibility :
    AdmissibleAlgebraicToClosedIrreducibilityStatement.{uG,uV,uH} := by
  intro G _ _ _ hcofinal V _ _ ρ hρ hirr b H _ _ _ π j hj hequiv hform
  let σ : Representation ℂ G H :=
    { toFun := fun g => (π g : H →ₗ[ℂ] H)
      map_one' := by ext x; simp
      map_mul' := fun g h => by ext x; simp }
  let J : ρ.IntertwiningMap σ := LinearMap.intertwiningMap_of_isIntertwiningMap ρ σ j hequiv
  have hrecover := admissibleSmoothVectorRecovery.{uG,uV,uH} G hcofinal V ρ hρ b H σ
    (fun g => (π g).continuous) J hj hform
  have hinvariant : ∀ (g : G) (x y : H), inner ℂ (π g x) (π g y) = inner ℂ x y := by
    intro g x y
    refine hj.induction_on₂
      (p := fun x y : H => inner ℂ (π g x) (π g y) = inner ℂ x y) ?_ ?_ x y
    · exact isClosed_eq
        (((π g).continuous.comp continuous_fst).inner ((π g).continuous.comp continuous_snd))
        (continuous_fst.inner continuous_snd)
    · intro v w
      rw [← hequiv, ← hequiv, hform, hform, b.invariant]
  have hinv_apply : ∀ (g : G) (x : H), π g (π g⁻¹ x) = x := by
    intro g x
    change (π g * π g⁻¹) x = x
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  have hinj : Function.Injective j := by
    refine (injective_iff_map_eq_zero j).2 fun v hv => b.definite v ?_
    rw [← hform, hv, inner_zero_left]
  refine ⟨?_, ?_⟩
  · have hV : Nontrivial V := by
      refine not_subsingleton_iff_nontrivial.1 fun hV =>
        (bot_ne_top : (⊥ : Subrepresentation ρ) ≠ ⊤) ?_
      ext v
      rw [Subsingleton.elim v 0]
      exact ⟨fun _ => Submodule.zero_mem _, fun _ => Submodule.zero_mem _⟩
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    exact ⟨⟨j v, 0, fun h => hv (hinj (h.trans j.map_zero.symm))⟩⟩
  · intro W hW hWinv
    have : IsClosed (W : Set H) := hW
    have hcomm : ∀ (g : G) (x : H), W.starProjection (π g x) = π g (W.starProjection x) := by
      intro g x
      refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
        (hWinv g _ (W.starProjection_apply_mem x)) fun w hw => ?_
      rw [← hinv_apply g w, ← (π g).map_sub, hinvariant]
      exact Submodule.starProjection_inner_eq_zero x _ (hWinv g⁻¹ w hw)
    let S : Subrepresentation ρ :=
      ⟨W.comap j, fun g v hv => by
        change j (ρ g v) ∈ W
        rw [hequiv]
        exact hWinv g _ hv⟩
    rcases hirr.eq_bot_or_eq_top S with hS | hS
    · left
      have hzero : ∀ v : V, W.starProjection (j v) = 0 := by
        intro v
        obtain ⟨K, hK⟩ := hρ.1 v
        obtain ⟨v', hv'⟩ := (hrecover (W.starProjection (j v))).1 ⟨K, fun k => by
          change π (k : G) (W.starProjection (j v)) = W.starProjection (j v)
          rw [← hcomm, ← hequiv]
          exact congrArg (fun x => W.starProjection (j x)) (hK k)⟩
        change j v' = W.starProjection (j v) at hv'
        have hv'S : v' ∈ S := by
          change j v' ∈ W
          rw [hv']
          exact W.starProjection_apply_mem _
        rw [hS] at hv'S
        change v' ∈ (⊥ : Submodule ℂ V) at hv'S
        rw [← hv', (Submodule.mem_bot ℂ).1 hv'S, map_zero]
      have hP : ∀ x : H, W.starProjection x = 0 := fun x =>
        hj.induction_on (p := fun x => W.starProjection x = 0) x
          (isClosed_eq W.starProjection.continuous continuous_const) hzero
      rw [Submodule.eq_bot_iff]
      intro w hw
      rw [← Submodule.starProjection_eq_self_iff.mpr hw]
      exact hP w
    · right
      have hrange : Set.range j ⊆ W := by
        rintro _ ⟨v, rfl⟩
        have hvS : v ∈ S := by
          rw [hS]
          trivial
        exact hvS
      have hclosure := closure_minimal hrange hW
      rw [hj.closure_range] at hclosure
      rw [Submodule.eq_top_iff']
      exact fun x => hclosure (Set.mem_univ x)

end Langlands
