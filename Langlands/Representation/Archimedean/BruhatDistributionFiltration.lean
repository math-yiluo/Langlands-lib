import Langlands.Analysis.DistributionLocalVanishing
import Langlands.Group.GL.UpperBruhatFiltrationGeometryProof
import Langlands.Representation.Archimedean.BruhatLowerCellVanishing

/-! # Descending the finite Bruhat filtration for a Whittaker distribution -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000

open Set
open Langlands.Analysis Langlands.GeneralLinear Langlands.HarmonicAnalysis
open scoped Distributions Matrix.Norms.Operator

namespace Langlands.Archimedean

universe u

variable {F : Type u} [RCLike F] {r : ℕ}

local notation "rankSize" => r + 1
local notation "M" => Matrix (Fin (r + 1)) (Fin (r + 1)) F
local notation "G" => Langlands.GeneralLinear (r + 1) F
local notation "D" => 𝓓(matrixUnitsOpen F (r + 1), ℂ)

private theorem inversionCount_le_long (w : Equiv.Perm (Fin (r + 1))) :
    permutationInversionCount rankSize w ≤ permutationInversionCount rankSize Fin.revPerm := by
  rw [permutationInversionCount_eq_card_permutationInversions,
    permutationInversionCount_eq_card_permutationInversions]
  apply Finset.card_le_card
  intro p hp
  have h := (mem_permutationInversions_iff rankSize w p).mp hp
  exact (mem_permutationInversions_iff rankSize Fin.revPerm p).mpr ⟨h.1, Fin.rev_lt_rev.mpr h.1⟩

private theorem isOpen_bruhatLongCellMatrixSet : IsOpen (bruhatCellMatrixSet F (Fin.revPerm (n := rankSize))) := by
  have hc : upperBruhatCellNeighborhood rankSize F (Fin.revPerm (n := rankSize)) = upperBruhatCell rankSize F Fin.revPerm := by
    ext g
    constructor
    · rintro (hg | ⟨v, hv, _⟩)
      · exact hg
      · exact ((not_lt_of_ge (inversionCount_le_long v)) hv).elim
    · exact Or.inl
  rw [bruhatCellMatrixSet_eq_image, ← hc]
  exact Units.isOpenEmbedding_val.isOpenMap _ (isOpen_upperBruhatCellNeighborhood Fin.revPerm)

/-- A left Whittaker distribution with a scalar trace Casimir vanishes
everywhere once it vanishes on the long Weyl cell. -/
theorem matrixDistribution_eq_zero_of_vanishing_longCell
    (ψ : UnitaryAdditiveCharacter F) (T : D →L[ℂ] ℂ) (eigenvalue : ℂ)
    (hCas : ∀ f : D, T (matrixTraceTestCasimir F rankSize f) = eigenvalue * T f)
    (hCov : ∀ (u : upperUnipotent rankSize F) (f : D),
      T (matrixLeftTranslateTest u.val f) = (Langlands.Whittaker.standardCharacter ψ r u : ℂ) * T f)
    (hLong : Distribution.IsVanishingOn T (bruhatCellMatrixSet F (Fin.revPerm (n := rankSize)))) :
    T = 0 := by
  obtain ⟨a, b, hψ, hc⟩ := exists_whittakerRootPhase ψ
  have : FiniteDimensional ℝ M := FiniteDimensional.trans ℝ F M
  have hl : ∀ (k : ℕ) (w : Equiv.Perm (Fin (r + 1))),
      rankSize * rankSize - permutationInversionCount rankSize w = k →
      ∀ x ∈ bruhatCellMatrixSet F w,
        ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ Distribution.IsVanishingOn T U := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro w hk x hx
      by_cases hw : w = Fin.revPerm
      · subst w
        exact ⟨_, isOpen_bruhatLongCellMatrixSet, hx, hLong⟩
      · let O := (Units.val : G → M) '' upperBruhatCellNeighborhood rankSize F w
        have hO : IsOpen O :=
          Units.isOpenEmbedding_val.isOpenMap _ (isOpen_upperBruhatCellNeighborhood w)
        have hOΩ : O ⊆ matrixUnitsOpen F rankSize := by
          rintro y ⟨g, _, rfl⟩
          exact g.isUnit
        have hTO : Distribution.IsVanishingOn T (O \ bruhatCellMatrixSet F w) := by
          apply isVanishingOn_of_locallyVanishing T
          rintro y ⟨⟨g, hg, rfl⟩, hy⟩
          rcases hg with hg | ⟨v, hv, hgv⟩
          · exact (hy ⟨⟨g, hg⟩, rfl⟩).elim
          · have hb := UpperBruhatBoundary.permutationInversionCount_le v
            have hvk : rankSize * rankSize - permutationInversionCount rankSize v < k := by omega
            exact ih _ hvk v rfl g.val ⟨⟨g, hgv⟩, rfl⟩
        obtain ⟨g, hg⟩ := hx
        let c := UpperBruhatCoordinates.cellHomeomorph (K := F) w
        let γ := (c.symm g).1
        let v := (c.symm g).2
        let P := permutation rankSize F w
        have hxO : x ∈ O := ⟨g.val, Or.inl g.property, hg⟩
        have hprod : γ.val.val * (P * v.val).val = x := by
          have he := congrArg (fun z : UpperBruhatCell rankSize F w => z.val.val) (c.apply_symm_apply g)
          change (γ.val * P * v.val).val = g.val.val at he
          rw [mul_assoc] at he
          exact he.trans hg
        have hbase : γ.val.val * (P * v.val).val ∈ O := by rwa [hprod]
        obtain ⟨U, hU, hxU, -, hTU⟩ :=
          matrixDistribution_vanishing_near_lowerBruhatCell hw a b ψ hψ hc T eigenvalue
            hCas hCov γ v hO hOΩ hbase hTO
        exact ⟨U, hU, hprod ▸ hxU, hTU⟩
  have hvan : Distribution.IsVanishingOn T (matrixUnitsOpen F rankSize : Set M) := by
    apply isVanishingOn_of_locallyVanishing T
    intro x hx
    obtain ⟨g, rfl⟩ := (show IsUnit x from hx)
    obtain ⟨w, hw⟩ := exists_mem_upperBruhatCell g
    exact hl _ w rfl g.val ⟨⟨g, hw⟩, rfl⟩
  apply ContinuousLinearMap.ext
  intro f
  exact hvan f f.tsupport_subset

/-- Two left Whittaker distributions with the same Casimir eigenvalue
agree everywhere if their values agree on tests in the long cell. -/
theorem matrixDistribution_eq_of_agree_on_longCell
    (ψ : UnitaryAdditiveCharacter F) (T S : D →L[ℂ] ℂ) (eigenvalue : ℂ)
    (hTCas : ∀ f : D, T (matrixTraceTestCasimir F rankSize f) = eigenvalue * T f)
    (hSCas : ∀ f : D, S (matrixTraceTestCasimir F rankSize f) = eigenvalue * S f)
    (hTCov : ∀ (u : upperUnipotent rankSize F) (f : D),
      T (matrixLeftTranslateTest u.val f) = (Langlands.Whittaker.standardCharacter ψ r u : ℂ) * T f)
    (hSCov : ∀ (u : upperUnipotent rankSize F) (f : D),
      S (matrixLeftTranslateTest u.val f) = (Langlands.Whittaker.standardCharacter ψ r u : ℂ) * S f)
    (hAgree : ∀ f : D, tsupport f ⊆ bruhatCellMatrixSet F (Fin.revPerm (n := rankSize)) → T f = S f) :
    T = S := by
  apply sub_eq_zero.mp
  apply matrixDistribution_eq_zero_of_vanishing_longCell ψ (T - S) eigenvalue
  · intro f
    change T _ - S _ = eigenvalue * (T f - S f)
    rw [hTCas, hSCas, mul_sub]
  · intro u f
    change T _ - S _ = _ * (T f - S f)
    rw [hTCov, hSCov, mul_sub]
  · intro f hf
    change T f - S f = 0
    rw [hAgree f hf, sub_self]

end Langlands.Archimedean
