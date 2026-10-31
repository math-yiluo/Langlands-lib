import Langlands.Representation.Derivative.MirabolicHighestDerivativePairingProof

/-!
# Derivative levels under a nondegenerate mirabolic pairing

These internal corollaries use the published highest-derivative pairing theorem.
A determinant-covariant pairing nondegenerate in its first representation bounds
that representation's derivative level by the second representation's level.
-/

noncomputable section

namespace Langlands.Derivative.Mirabolic

open GeneralLinear HarmonicAnalysis

open scoped NNReal

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
variable (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)

/-- Choose an invariant highest-derivative pairing, bundled with its left
nondegeneracy, from the published existence theorem. -/
def chooseHighestDerivativePairing (N k : ℕ) (hk : 0 < k ∧ k ≤ N + 1) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier))
      (B : SmoothRep.{0, uF, uW} ℂ (mirabolic N F.Carrier)),
      Nontrivial ((mirabolicDerivativeOfOrder T ψ N k hk).obj A) →
      (∀ (j : ℕ) (hj : 0 < j ∧ j ≤ N + 1), k < j →
        Subsingleton ((mirabolicDerivativeOfOrder T ψ N j hj).obj A)) →
      ∀ β : InvariantBilinear.forms A.representation B.representation
          (fun g => ((((T.determinantNorm (N + 1)) g.val : ℝ≥0) : ℝ) : ℂ)),
        (∀ v : A, (∀ w : B, β.val v w = 0) → v = 0) →
        { γ : InvariantBilinear.forms
            ((mirabolicDerivativeOfOrder T ψ N k hk).obj A).representation
            ((mirabolicDerivativeOfOrder T ψ N k hk).obj B).representation
            (fun _ => (1 : ℂ)) //
          ∀ v : (mirabolicDerivativeOfOrder T ψ N k hk).obj A,
            (∀ w : (mirabolicDerivativeOfOrder T ψ N k hk).obj B,
              γ.val v w = 0) → v = 0 } := by
  letI := T.topology
  intro A B hA hhigh β hβ
  exact ⟨Classical.choose (mirabolicHighestDerivativePairing F T ψ N A B k hk hA hhigh β hβ),
    Classical.choose_spec (mirabolicHighestDerivativePairing F T ψ N A B k hk hA hhigh β hβ)⟩

/-- At the highest nonzero derivative order of the first representation, a
left-nondegenerate determinant-covariant pairing forces the second derivative
to be nonzero. -/
theorem nontrivial_derivative_of_highestPairing (N k : ℕ)
    (hk : 0 < k ∧ k ≤ N + 1) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier))
      (B : SmoothRep.{0, uF, uW} ℂ (mirabolic N F.Carrier)),
      Nontrivial ((mirabolicDerivativeOfOrder T ψ N k hk).obj A) →
      (∀ (j : ℕ) (hj : 0 < j ∧ j ≤ N + 1), k < j →
        Subsingleton ((mirabolicDerivativeOfOrder T ψ N j hj).obj A)) →
      ∀ β : InvariantBilinear.forms A.representation B.representation
          (fun g => ((((T.determinantNorm (N + 1)) g.val : ℝ≥0) : ℝ) : ℂ)),
        (∀ v : A, (∀ w : B, β.val v w = 0) → v = 0) →
        Nontrivial ((mirabolicDerivativeOfOrder T ψ N k hk).obj B) := by
  let := T.topology
  intro A B hA hhigh β hβ
  obtain ⟨γ, hγ⟩ := chooseHighestDerivativePairing T ψ N k hk A B hA hhigh β hβ
  by_contra hB
  let := not_nontrivial_iff_subsingleton.mp hB
  have hzero : ∀ v : (mirabolicDerivativeOfOrder T ψ N k hk).obj A, v = 0 := by
    intro v
    apply hγ v
    intro w
    rw [Subsingleton.elim w 0]
    exact map_zero (γ.val v)
  obtain ⟨v, w, hvw⟩ := hA.exists_pair_ne
  exact hvw ((hzero v).trans (hzero w).symm)

/-- A determinant-covariant pairing nondegenerate in the first representation
bounds its derivative level by the second representation's level. -/
theorem level_le_of_nondegeneratePairing {N : ℕ} :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier))
      (B : SmoothRep.{0, uF, uW} ℂ (mirabolic N F.Carrier))
      (β : InvariantBilinear.forms A.representation B.representation
        (fun g => ((((T.determinantNorm (N + 1)) g.val : ℝ≥0) : ℝ) : ℂ))),
      (∀ v : A, (∀ w : B, β.val v w = 0) → v = 0) →
      level T ψ A ≤ level T ψ B := by
  let := T.topology
  intro A B β hβ
  by_cases hzero : level T ψ A = 0
  · rw [hzero]
    exact Nat.zero_le _
  have hpos : 0 < level T ψ A := Nat.pos_of_ne_zero hzero
  obtain ⟨hle, hnonzero, hhigh⟩ := (level_eq_iff T ψ hpos A).mp rfl
  let hk : 0 < level T ψ A ∧ level T ψ A ≤ N + 1 := ⟨hpos, hle⟩
  have hA := (hasNonzeroDerivative_iff T ψ hk A).mp hnonzero
  have hvan : ∀ (j : ℕ) (hj : 0 < j ∧ j ≤ N + 1), level T ψ A < j →
      Subsingleton ((mirabolicDerivativeOfOrder T ψ N j hj).obj A) := by
    intro j hj hlt
    apply not_nontrivial_iff_subsingleton.mp
    intro hn
    exact hhigh hlt hj.2 ((hasNonzeroDerivative_iff T ψ hj A).mpr hn)
  have hB := nontrivial_derivative_of_highestPairing T ψ N (level T ψ A) hk
    A B hA hvan β hβ
  exact le_level_of_hasNonzeroDerivative T ψ B ⟨hk, hB⟩

end Langlands.Derivative.Mirabolic
