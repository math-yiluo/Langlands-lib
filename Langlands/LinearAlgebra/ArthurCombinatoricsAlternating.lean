import Langlands.LinearAlgebra.ArthurCombinatoricsStatement

/-!
# Arthur's alternating-sum identity and the expansion of `τ τ̂` in `σ`

Arthur 1978, Proposition 1.1, and Arthur 2005, (8.2).

* `alternatingSum_eq`, `alternatingSumStatement`: for `Θ₁ ⊆ Θ₂`,
  `∑_{Θ₁ ⊆ Θ ⊆ Θ₂} (−1)^{|Θ₂ \ Θ|}` is `1` if `Θ₁ = Θ₂` and `0` otherwise.
* `tauTauHatSigmaExpansionStatement`: `τ_{P_1}^P(H) τ̂_P(H) = ∑_{P_2 ⊇ P} σ_{P_1}^{P_2}(H)`.
-/

noncomputable section

universe u

set_option autoImplicit false

namespace Langlands.ArthurCombinatorics

/-- Arthur 1978, Proposition 1.1, for finite sets of any type. -/
theorem alternatingSum_eq {ι : Type*} [DecidableEq ι] (Θ₁ Θ₂ : Finset ι) (h : Θ₁ ⊆ Θ₂) :
    ∑ Θ ∈ Θ₂.powerset.filter (Θ₁ ⊆ ·), (-1 : ℤ) ^ (Θ₂ \ Θ).card =
      if Θ₁ = Θ₂ then 1 else 0 := by
  have hbij : ∑ Θ ∈ Θ₂.powerset.filter (Θ₁ ⊆ ·), (-1 : ℤ) ^ (Θ₂ \ Θ).card =
      ∑ T ∈ (Θ₂ \ Θ₁).powerset, (-1 : ℤ) ^ T.card := by
    refine Finset.sum_nbij' (fun Θ => Θ₂ \ Θ) (fun T => Θ₂ \ T) ?_ ?_ ?_ ?_ ?_
    · intro Θ hΘ
      rw [Finset.mem_filter, Finset.mem_powerset] at hΘ
      rw [Finset.mem_powerset]
      exact Finset.sdiff_subset_sdiff le_rfl hΘ.2
    · intro T hT
      rw [Finset.mem_powerset] at hT
      rw [Finset.mem_filter, Finset.mem_powerset]
      refine ⟨Finset.sdiff_subset, fun x hx => Finset.mem_sdiff.mpr ⟨h hx, fun hxT => ?_⟩⟩
      exact (Finset.mem_sdiff.mp (hT hxT)).2 hx
    · intro Θ hΘ
      rw [Finset.mem_filter, Finset.mem_powerset] at hΘ
      exact Finset.sdiff_sdiff_eq_self hΘ.1
    · intro T hT
      rw [Finset.mem_powerset] at hT
      exact Finset.sdiff_sdiff_eq_self (hT.trans Finset.sdiff_subset)
    · intro Θ _
      rfl
  have hiff : Θ₂ \ Θ₁ = ∅ ↔ Θ₁ = Θ₂ :=
    ⟨fun he => Finset.Subset.antisymm h (Finset.sdiff_eq_empty_iff_subset.mp he),
      fun he => by rw [he, Finset.sdiff_self]⟩
  rw [hbij, Finset.sum_powerset_neg_one_pow_card]
  simp only [hiff]

/-- **Arthur 1978, Proposition 1.1.** -/
theorem alternatingSumStatement : AlternatingSumStatement.{u} :=
  fun Θ₁ Θ₂ h => alternatingSum_eq Θ₁ Θ₂ h

/-- **Arthur 2005, (8.2).** `τ_{P_1}^P(H) τ̂_P(H) = ∑_{P_2 ⊇ P} σ_{P_1}^{P_2}(H)`: inserting the
definition of `σ` and exchanging the two sums, the inner sum over `P ⊆ P_2 ⊆ P_3` is the
alternating sum of Proposition 1.1, which is `1` exactly when `P_3 = P`. -/
theorem tauTauHatSigmaExpansionStatement : TauTauHatSigmaExpansionStatement.{u} := by
  intro ι M N _ _ _ _ _ _ P _ _ b Θ₁ ΘP _ hP H
  classical
  set S := b.support
  have hcomm : ∑ Θ₂ ∈ S.powerset.filter (ΘP ⊆ ·), sigma P S Θ₁ Θ₂ H =
      ∑ Θ₃ ∈ S.powerset.filter (ΘP ⊆ ·), ∑ Θ₂ ∈ Θ₃.powerset.filter (ΘP ⊆ ·),
        (-1 : ℤ) ^ (Θ₃ \ Θ₂).card * tau P Θ₁ Θ₃ H * tauHat P Θ₃ S H := by
    unfold sigma
    refine Finset.sum_comm' fun Θ₂ Θ₃ => ?_
    simp only [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨⟨h2S, hP2⟩, h3S, h23⟩
      exact ⟨⟨h23, hP2⟩, h3S, hP2.trans h23⟩
    · rintro ⟨⟨h23, hP2⟩, h3S, -⟩
      exact ⟨⟨h23.trans h3S, hP2⟩, h3S, h23⟩
  rw [hcomm]
  have hinner : ∀ Θ₃ ∈ S.powerset.filter (ΘP ⊆ ·),
      ∑ Θ₂ ∈ Θ₃.powerset.filter (ΘP ⊆ ·),
          (-1 : ℤ) ^ (Θ₃ \ Θ₂).card * tau P Θ₁ Θ₃ H * tauHat P Θ₃ S H =
        if ΘP = Θ₃ then tau P Θ₁ Θ₃ H * tauHat P Θ₃ S H else 0 := by
    intro Θ₃ hΘ₃
    have hP3 : ΘP ⊆ Θ₃ := (Finset.mem_filter.mp hΘ₃).2
    rw [← Finset.sum_mul, ← Finset.sum_mul, alternatingSum_eq ΘP Θ₃ hP3]
    split_ifs <;> ring
  have hmem : ΘP ∈ S.powerset.filter (ΘP ⊆ ·) :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hP, subset_refl _⟩
  rw [Finset.sum_congr rfl hinner, Finset.sum_ite_eq]
  simp only [hmem, ↓reduceIte]

end Langlands.ArthurCombinatorics
