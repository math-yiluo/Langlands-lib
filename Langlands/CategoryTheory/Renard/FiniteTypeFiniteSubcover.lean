import Langlands.CategoryTheory.Renard.FiniteTypeFiniteSubcoverStatements
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.Zorn

namespace Langlands.Renard

open CategoryTheory

universe u v

noncomputable section

section OrderArgument

variable {α : Type*} [CompleteLattice α]

/-- The nonempty proper-chain condition forces every top cover to have a
finite subcover. -/
private theorem finiteSubcover_of_proper_chains
    (hchain : ∀ D : Set α, D.Nonempty → IsChain (· ≤ ·) D →
      (∀ x ∈ D, x ≠ ⊤) → ¬ IsLUB D ⊤)
    (S : Set α) (hS : IsLUB S ⊤) :
    ∃ F : Finset α, (F : Set α) ⊆ S ∧ IsLUB (F : Set α) ⊤ := by
  classical
  by_contra hno
  let U : Set α := {x | ∀ F : Finset α, (F : Set α) ⊆ S →
    x ⊔ sSup (F : Set α) ≠ ⊤}
  have hbot : (⊥ : α) ∈ U := by
    intro F hF heq
    exact hno ⟨F, hF, isLUB_iff_sSup_eq.mpr (by simpa only [bot_sup_eq] using heq)⟩
  obtain ⟨m, hm⟩ := zorn_le₀ U (by
    intro c hc hcc
    rcases c.eq_empty_or_nonempty with rfl | hcn
    · exact ⟨⊥, hbot, by simp⟩
    refine ⟨sSup c, ?_, fun x hx => le_sSup hx⟩
    intro F hF heq
    let D : Set α := (fun x => x ⊔ sSup (F : Set α)) '' c
    have hDn : D.Nonempty := hcn.image _
    have hDc : IsChain (· ≤ ·) D := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _
      rcases hcc.total ha hb with hab | hba
      · exact Or.inl (sup_le_sup_right hab _)
      · exact Or.inr (sup_le_sup_right hba _)
    have hproper : ∀ x ∈ D, x ≠ ⊤ := by
      rintro _ ⟨a, ha, rfl⟩
      exact hc ha F hF
    have hL : IsLUB D (sSup c ⊔ sSup (F : Set α)) := by
      constructor
      · rintro _ ⟨a, ha, rfl⟩
        exact sup_le_sup_right (le_sSup ha) _
      · intro q hq
        obtain ⟨a, ha⟩ := hcn
        refine sup_le (sSup_le fun b hb => ?_) ?_
        · exact le_sup_left.trans (hq ⟨b, hb, rfl⟩)
        · exact le_sup_right.trans (hq ⟨a, ha, rfl⟩)
    exact hchain D hDn hDc hproper (heq ▸ hL))
  have hmem : ∀ a ∈ S, a ≤ m := by
    intro a ha
    have hma : m ⊔ a ∈ U := by
      intro F hF
      have hins : (↑(insert a F) : Set α) ⊆ S := by
        intro b hb
        rcases Finset.mem_insert.mp hb with rfl | hb
        · exact ha
        · exact hF hb
      have h := hm.1 (insert a F) hins
      simpa only [Finset.coe_insert, sSup_insert, sup_assoc] using h
    exact le_sup_right.trans (hm.2 hma le_sup_left)
  have hmt : m = ⊤ := le_antisymm le_top (hS.2 hmem)
  exact hm.1 ∅ (by simp)
    (by simpa only [Finset.coe_empty, sSup_empty, sup_bot_eq] using hmt)

/-- A finite subset of a nonempty chain has an upper bound inside the chain. -/
private theorem finite_upperBound_in_chain {S : Set α} (hSn : S.Nonempty)
    (hSc : IsChain (· ≤ ·) S) (F : Finset α) (hF : (F : Set α) ⊆ S) :
    ∃ a ∈ S, ∀ b ∈ F, b ≤ a := by
  classical
  revert hF
  induction F using Finset.induction_on with
  | empty =>
    intro _
    obtain ⟨a, ha⟩ := hSn
    exact ⟨a, ha, by simp⟩
  | @insert a F _ ih =>
    intro hF
    have ha : a ∈ S := hF (by simp)
    obtain ⟨b, hb, hFb⟩ := ih (by
      intro x hx
      exact hF (by simpa using Finset.mem_insert_of_mem hx))
    rcases hSc.total ha hb with hab | hba
    · refine ⟨b, hb, ?_⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hab
      · exact hFb x hx
    · refine ⟨a, ha, ?_⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact le_rfl
      · exact (hFb x hx).trans hba

private theorem proper_chains_of_finiteSubcover
    (hcover : ∀ S : Set α, IsLUB S ⊤ →
      ∃ F : Finset α, (F : Set α) ⊆ S ∧ IsLUB (F : Set α) ⊤) :
    ∀ S : Set α, S.Nonempty → IsChain (· ≤ ·) S →
      (∀ x ∈ S, x ≠ ⊤) → ¬ IsLUB S ⊤ := by
  intro S hSn hSc hproper htop
  obtain ⟨F, hFS, hFt⟩ := hcover S htop
  obtain ⟨a, ha, hFa⟩ := finite_upperBound_in_chain hSn hSc F hFS
  exact hproper a ha (le_antisymm le_top (hFt.2 hFa))

end OrderArgument

variable {C : Type u} [Category.{v} C]

/-- Choose subobject joins internally, retaining the original order and top. -/
@[instance_reducible] private def subobjectCompleteLattice (X : C)
    (hX : HasSubobjectUnions X) : CompleteLattice (Subobject X) := by
  letI : SupSet (Subobject X) := ⟨fun S => (hX S).choose⟩
  exact { completeLatticeOfSup (Subobject X) (fun S => (hX S).choose_spec) with
    top := (⊤ : Subobject X)
    le_top := fun _ => le_top }

/-- Renard A.I.3: the source chain definition is the finite-subcover condition. -/
theorem finiteTypeFiniteSubcover (C : Type u) [Category.{v} C] :
    FiniteTypeFiniteSubcoverStatement C := by
  intro X
  constructor
  · intro hX
    let := subobjectCompleteLattice X hX.1
    exact ⟨hX.1, finiteSubcover_of_proper_chains (α := Subobject X) hX.2⟩
  · intro hX
    let := subobjectCompleteLattice X hX.1
    exact ⟨hX.1, proper_chains_of_finiteSubcover (α := Subobject X) hX.2⟩

end

end Langlands.Renard
