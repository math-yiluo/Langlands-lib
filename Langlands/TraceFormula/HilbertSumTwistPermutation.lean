import Langlands.TraceFormula.UnitarySchurHilbertSumProof
import Langlands.TraceFormula.SmoothingEigenspaceHilbertSum
import Langlands.Analysis.HilbertSumTraceProof

/-! # Permutation of irreducible Hilbert summands by a twist -/

noncomputable section

namespace Langlands.TraceFormula

open Langlands.Analysis.OperatorIdeals

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {G : Type v} [Group G] (ρ : G →* (H →L[ℂ] H))

omit [CompleteSpace H] in
private theorem irreducibleSubspace_map_twist (θ : G ≃* G) (U : H ≃ₗᵢ[ℂ] H)
    (hU : ∀ g x, U (ρ g x) = ρ (θ g) (U x)) (P : Submodule ℂ H)
    (hP : P ≠ ⊥ ∧ IsClosed (P : Set H) ∧ (∀ a x, x ∈ P → ρ a x ∈ P) ∧
      ∀ Q : Submodule ℂ H, Q ≤ P → IsClosed (Q : Set H) →
        (∀ a x, x ∈ Q → ρ a x ∈ Q) → Q = ⊥ ∨ Q = P) :
    let S := P.map U.toLinearEquiv.toLinearMap
    S ≠ ⊥ ∧ IsClosed (S : Set H) ∧ (∀ a x, x ∈ S → ρ a x ∈ S) ∧
      ∀ Q : Submodule ℂ H, Q ≤ S → IsClosed (Q : Set H) →
        (∀ a x, x ∈ Q → ρ a x ∈ Q) → Q = ⊥ ∨ Q = S := by
  intro S
  obtain ⟨hP0, hPc, hPi, hPirred⟩ := hP
  refine ⟨Submodule.map_ne_bot_iff.mpr hP0, U.toHomeomorph.isClosedMap _ hPc, ?_, ?_⟩
  · rintro a _ ⟨x, hx, rfl⟩
    refine ⟨ρ (θ.symm a) x, hPi _ _ hx, ?_⟩
    change U (ρ (θ.symm a) x) = ρ a (U x)
    rw [hU, θ.apply_symm_apply]
  · intro Q hQS hQc hQi
    let Q₀ := Q.comap U.toLinearEquiv.toLinearMap
    have hQ₀P : Q₀ ≤ P := by
      change Q.comap U.toLinearEquiv.toLinearMap ≤ P
      rw [← Submodule.comap_map_eq_of_injective U.injective P]
      exact Submodule.comap_mono hQS
    have hQ₀i : ∀ a x, x ∈ Q₀ → ρ a x ∈ Q₀ := by
      intro a x hx
      change U (ρ a x) ∈ Q
      rw [hU]
      exact hQi _ _ hx
    have hMap : Q₀.map U.toLinearEquiv.toLinearMap = Q :=
      Submodule.map_comap_eq_of_surjective U.surjective Q
    rcases hPirred Q₀ hQ₀P (hQc.preimage U.continuous) hQ₀i with h | h
    · left
      rw [← hMap, h, Submodule.map_bot]
    · right
      rw [← hMap, h]

/-- On a multiplicity-one unitary Hilbert sum, a unitary intertwiner for a
group automorphism permutes the chosen irreducible invariant summands. -/
def HilbertSumTwistPermutationStatement : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (G : Type v) [Group G] (ρ : G →* (H →L[ℂ] H)),
    (∀ a x, ‖ρ a x‖ = ‖x‖) →
    let Irred (P : Submodule ℂ H) :=
      P ≠ ⊥ ∧ IsClosed (P : Set H) ∧ (∀ a x, x ∈ P → ρ a x ∈ P) ∧
        ∀ Q : Submodule ℂ H, Q ≤ P → IsClosed (Q : Set H) →
          (∀ a x, x ∈ Q → ρ a x ∈ Q) → Q = ⊥ ∨ Q = P
    ∀ (A : Set (Submodule ℂ H)) [∀ P : A, CompleteSpace (P : Submodule ℂ H)],
    (∀ P ∈ A, Irred P) →
    IsHilbertSum ℂ (fun P : A => (P : Submodule ℂ H)) (fun P => P.val.subtypeₗᵢ) →
    (∀ P Q, Irred P → Irred Q → ∀ (hPi : ∀ a x, x ∈ P → ρ a x ∈ P) (e : P ≃ₗᵢ[ℂ] Q),
      (∀ a (x : P), (e ⟨ρ a x, hPi a x x.2⟩ : H) = ρ a (e x)) → P = Q) →
    ∀ (θ : G ≃* G) (U : H ≃ₗᵢ[ℂ] H),
      (∀ a x, U (ρ a x) = ρ (θ a) (U x)) →
      ∃ τ : A ≃ A, ∀ P : A, P.val.map U.toLinearEquiv.toLinearMap = (τ P : Submodule ℂ H)

theorem hilbertSumTwistPermutation : HilbertSumTwistPermutationStatement.{u,v} := by
  intro H _ _ _ G _ ρ hρ Irred A _ hP hSum hOne θ U hU
  have hMember (η : G ≃* G) (V : H ≃ₗᵢ[ℂ] H)
      (hV : ∀ a x, V (ρ a x) = ρ (η a) (V x)) (P : A) :
      P.val.map V.toLinearEquiv.toLinearMap ∈ A := by
    let Q := P.val.map V.toLinearEquiv.toLinearMap
    have hQ : Irred Q := irreducibleSubspace_map_twist ρ η V hV P.val (hP _ P.property)
    obtain ⟨R, hR, e, he⟩ :=
      unitarySchurHilbertSum.2 H G ρ hρ A
        (fun P hP' => ⟨(hP P hP').2.2.1, (hP P hP').2.2.2⟩) hSum
        Q hQ.1 hQ.2.1 hQ.2.2.1 hQ.2.2.2
    change Q ∈ A
    rw [hOne Q R hQ (hP R hR) hQ.2.2.1 e he]
    exact hR
  have hUinv (a : G) (x : H) : U.symm (ρ a x) = ρ (θ.symm a) (U.symm x) := by
    apply U.injective
    rw [U.apply_symm_apply, hU, θ.apply_symm_apply, U.apply_symm_apply]
  let τ : A ≃ A :=
    { toFun P := ⟨P.val.map U.toLinearEquiv.toLinearMap, hMember θ U hU P⟩
      invFun P := ⟨P.val.map U.symm.toLinearEquiv.toLinearMap, hMember θ.symm U.symm hUinv P⟩
      left_inv P := by
        apply Subtype.ext
        change (P.val.map U.toLinearEquiv.toLinearMap).map U.symm.toLinearEquiv.toLinearMap = P.val
        have h : U.symm.toLinearEquiv.toLinearMap.comp U.toLinearEquiv.toLinearMap = LinearMap.id := by
          ext1 x
          exact U.symm_apply_apply x
        rw [← Submodule.map_comp, h, Submodule.map_id]
      right_inv P := by
        apply Subtype.ext
        change (P.val.map U.symm.toLinearEquiv.toLinearMap).map U.toLinearEquiv.toLinearMap = P.val
        have h : U.toLinearEquiv.toLinearMap.comp U.symm.toLinearEquiv.toLinearMap = LinearMap.id := by
          ext1 x
          exact U.apply_symm_apply x
        rw [← Submodule.map_comp, h, Submodule.map_id] }
  exact ⟨τ, fun _ => rfl⟩

/-- The diagonal compression of a twisted product vanishes on a summand moved
by the twist if the left factor preserves all summands. -/
theorem summandCompression_mul_twist_eq_zero {J : Type v} (W : J → Submodule ℂ H)
    [∀ j, CompleteSpace (W j)] (hW : IsHilbertSum ℂ (fun j => W j) (fun j => (W j).subtypeₗᵢ))
    (A U : H →L[ℂ] H) (τ : J → J)
    (hA : ∀ j x, x ∈ W j → A x ∈ W j) (hU : ∀ j x, x ∈ W j → U x ∈ W (τ j))
    (j : J) (hj : τ j ≠ j) :
    summandCompression (W j) (A * U) = 0 :=
  compression_eq_zero_of_ne W hW (A * U) τ
    (fun i x hx => hA (τ i) (U x) (hU i x hx)) j hj

end Langlands.TraceFormula
