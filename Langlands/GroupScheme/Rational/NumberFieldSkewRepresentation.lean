import Langlands.GroupScheme.Rational.NumberFieldHigherRankSkewIsotropy

/-! # Local-to-global representation by skew-hermitian quaternion forms -/

noncomputable section

universe u

namespace Langlands.GroupScheme.Quaternionic

/-- A nonzero skew value represented at every completion by a nonsingular
  quaternion form of rank at least two is represented over the number field. -/
def NumberFieldSkewRepresentationStatement : Prop :=
  ∀ (F D : Type u) [Field F] [NumberField F] [DivisionRing D] [Algebra F D]
    [FiniteDimensional F D] [Algebra.IsCentral F D] (σ : FirstKindInvolution F D)
    (hdim : Module.finrank F D = 4) (hsym : Module.finrank F σ.symmetricSubspace = 3),
    let τ := σ.quaternionConjugation hdim hsym
    ∀ (n : ℕ), 2 ≤ n → ∀ (H : Matrix (Fin n) (Fin n) D), τ.IsAntihermitian H → IsUnit H →
    ∀ c : D, c ∈ τ.alternatingSubspace → c ≠ 0 → τ.IsLocallyRepresented H c →
      ∃ x, τ.sesqForm H x x = c

theorem numberFieldSkewRepresentation : NumberFieldSkewRepresentationStatement.{u} := by
  intro F D _ _ _ _ _ _ σ hdim hsym τ n hn H hH hu c hc hc0 hl
  by_cases hn₂ : n = 2
  · subst n
    exact numberFieldBinarySkewRepresentation F D σ hdim hsym H hH hu c hc hc0 hl
  let : Invertible (2 : F) := invertibleOfNonzero (two_ne_zero : (2 : F) ≠ 0)
  let H' := adjoinSkewLine H (-c)
  have hH' : τ.IsAntihermitian H' := hH.adjoinSkewLine (τ.alternatingSubspace.neg_mem hc)
  have hu' : IsUnit H' := adjoinSkewLine_isUnit hu
    (isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr hc0))
  have hcard : 4 ≤ Fintype.card (Fin (n + 1)) := by
    rw [Fintype.card_fin]
    omega
  obtain ⟨x, hx, hval⟩ := numberFieldHigherRankSkewIsotropy F D σ hdim hsym _ hcard H' hH' hu'
    (τ.isLocallyNonsingularIsotropic_adjoin_neg hl)
  exact τ.represents_of_adjoin_neg_isotropic hH hu c hc hx hval

end Langlands.GroupScheme.Quaternionic
