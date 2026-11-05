import Langlands.Representation.Unitary.CompactApproximationOrthogonalStatement
import Langlands.Representation.Unitary.CompactApproximationMinimalProof
import Mathlib.Order.Zorn

noncomputable section

namespace Langlands.Analysis

universe uG uE

theorem compactApproximationOrthogonal :
    CompactApproximationOrthogonalStatement.{uG, uE} := by
  classical
  intro G _ E _ _ _ π hunit T hcompact hsymm hlim hpres W hWclosed hWinv
  let Good : Submodule ℂ E → Prop := fun P =>
    P ≤ W ∧ P ≠ ⊥ ∧ IsClosed (P : Set E) ∧
      (∀ (g : G), ∀ x ∈ P, π g x ∈ P) ∧
      ∀ (Q : Submodule ℂ E), Q ≤ P → IsClosed (Q : Set E) →
        (∀ (g : G), ∀ x ∈ Q, π g x ∈ Q) → Q = ⊥ ∨ Q = P
  let Valid : Set (Set (Submodule ℂ E)) := {A |
    (∀ P ∈ A, Good P) ∧ A.Pairwise (fun P Q => P ⟂ Q)}
  have hchain : ∀ c ⊆ Valid, IsChain (· ⊆ ·) c →
      ∃ ub ∈ Valid, ∀ a ∈ c, a ⊆ ub := by
    intro c hc hcc
    refine ⟨⋃₀ c, ⟨?_, ?_⟩, ?_⟩
    · intro P hP
      obtain ⟨a, ha, hPa⟩ := Set.mem_sUnion.mp hP
      exact (hc ha).1 P hPa
    · intro P hP Q hQ hPQ
      obtain ⟨a, ha, hPa⟩ := Set.mem_sUnion.mp hP
      obtain ⟨b, hb, hQb⟩ := Set.mem_sUnion.mp hQ
      rcases hcc.total ha hb with hab | hba
      · exact (hc hb).2 (hab hPa) hQb hPQ
      · exact (hc ha).2 hPa (hba hQb) hPQ
    · intro a ha P hP
      exact Set.mem_sUnion.mpr ⟨a, ha, hP⟩
  obtain ⟨A, hA, hmax⟩ := zorn_subset Valid hchain
  rcases hA with ⟨hGood, hOrtho⟩
  let R : Submodule ℂ E := sSup A
  let K : Submodule ℂ E := R.topologicalClosure
  have hKclosed : IsClosed (K : Set E) := R.isClosed_topologicalClosure
  have hKW : K ≤ W :=
    R.topologicalClosure_minimal (sSup_le fun P hP => (hGood P hP).1) hWclosed
  have hPinK (P : Submodule ℂ E) (hP : P ∈ A) : P ≤ K :=
    (le_sSup hP).trans R.le_topologicalClosure
  have hKinv : ∀ (g : G), ∀ x ∈ K, π g x ∈ K := by
    intro g x hx
    have hle : R ≤ K.comap (π g).toLinearMap := by
      apply sSup_le
      intro P hP z hz
      exact hPinK P hP ((hGood P hP).2.2.2.1 g z hz)
    exact R.topologicalClosure_minimal hle (hKclosed.preimage (π g).continuous) hx
  refine ⟨A, hGood, hOrtho, ?_⟩
  change K = W
  by_contra hneq
  have : IsClosed (K : Set E) := hKclosed
  have horthinv : ∀ (g : G), ∀ x ∈ Kᗮ, π g x ∈ Kᗮ := by
    intro g x hx y hy
    have hinv : π g (π g⁻¹ y) = y := by
      change (π g * π g⁻¹) y = y
      rw [← map_mul, mul_inv_cancel, map_one]
      rfl
    rw [← hinv, hunit]
    exact hx _ (hKinv g⁻¹ y hy)
  have hNne : Kᗮ ⊓ W ≠ ⊥ := by
    intro hN
    have hsup := Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hKW
    exact hneq (by simpa only [hN, sup_bot_eq] using hsup)
  have hNclosed : IsClosed ((Kᗮ ⊓ W : Submodule ℂ E) : Set E) :=
    K.isClosed_orthogonal.inter hWclosed
  have hNinv : ∀ (g : G), ∀ x ∈ Kᗮ ⊓ W, π g x ∈ Kᗮ ⊓ W :=
    fun g x hx => ⟨horthinv g x hx.1, hWinv g x hx.2⟩
  obtain ⟨P, hPN, hPne, hPclosed, hPinv, hPminimal⟩ :=
    compactApproximationMinimal G E π hunit T hcompact hsymm hlim hpres
      (Kᗮ ⊓ W) hNne hNclosed hNinv
  have hPGood : Good P :=
    ⟨hPN.trans inf_le_right, hPne, hPclosed, hPinv, hPminimal⟩
  have hPK : P ⟂ K := hPN.trans inf_le_left
  have hPA : P ∉ A := by
    intro hPA
    apply hPne
    apply le_antisymm _ bot_le
    have hle : P ≤ K ⊓ Kᗮ := le_inf (hPinK P hPA) hPK
    simpa only [K.inf_orthogonal_eq_bot] using hle
  have hinsert : insert P A ∈ Valid := by
    constructor
    · intro Q hQ
      rcases Set.mem_insert_iff.mp hQ with rfl | hQ
      · exact hPGood
      · exact hGood Q hQ
    · intro Q hQ V hV hQV
      rcases Set.mem_insert_iff.mp hQ with hQP | hQA
      · subst Q
        rcases Set.mem_insert_iff.mp hV with rfl | hVA
        · exact (hQV rfl).elim
        · exact hPK.mono_right (hPinK V hVA)
      · rcases Set.mem_insert_iff.mp hV with hVP | hVA
        · subst V
          exact (hPK.mono_right (hPinK Q hQA)).symm
        · exact hOrtho hQA hVA hQV
  exact hPA (hmax hinsert (Set.subset_insert P A) (Set.mem_insert P A))

end Langlands.Analysis
