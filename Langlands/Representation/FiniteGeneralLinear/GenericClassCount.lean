import Langlands.Representation.FiniteGeneralLinear.HarishChandraSeries
import Langlands.Representation.FiniteGeneralLinear.GelfandGraev
import Langlands.Representation.Finite.MultiplicityFree
import Mathlib.Data.List.OfFn

/-! Gelfand–Graev constituents and weighted cuspidal multisets. -/

noncomputable section

open Module Representation
open scoped BigOperators

namespace Langlands.FiniteGeneralLinear

open FiniteRep GeneralLinear

variable {k : Type*} [Field k] {n : ℕ}

/-- Cuspidal multisets of total rank `n`. -/
abbrev CuspidalMultiset (n : ℕ) (k : Type*) [Field k] :=
  {m : Multiset (PositiveCuspidalLabel k) // (m.map cuspidalLabelRank).sum = n}

private theorem exists_datum_labels (m : CuspidalMultiset n k) :
    ∃ D : HarishChandraDatum n k, D.labels = m.val := by
  obtain ⟨m, hm⟩ := m
  obtain ⟨l, rfl⟩ := Quot.exists_rep m
  let B : BlockShape n :=
    { length := l.length
      size := fun i => cuspidalLabelRank (l.get i)
      positive := fun i => (l.get i).1.property
      sum_eq := by
        change ((Finset.univ : Finset (Fin l.length)).val.map
          (fun i => cuspidalLabelRank (l.get i))).sum = n
        rw [Fin.univ_val_map]
        change ((List.ofFn fun i : Fin l.length => cuspidalLabelRank l[i.val] :
          List ℕ) : Multiset ℕ).sum = n
        rw [List.ofFn_getElem_eq_map l (cuspidalLabelRank (k := k))]
        exact hm }
  let D : HarishChandraDatum n k := ⟨B, fun i => (l.get i).2⟩
  refine ⟨D, ?_⟩
  have he (i : Fin l.length) : D.blockLabel i = l.get i := by
    change (⟨⟨cuspidalLabelRank (l.get i), (l.get i).1.property⟩, (l.get i).2⟩ :
      PositiveCuspidalLabel k) = l.get i
    cases l.get i
    rfl
  change Finset.univ.val.map D.blockLabel = (l : Multiset (PositiveCuspidalLabel k))
  rw [Fin.univ_val_map]
  have h := List.ofFn_get l
  rw [show D.blockLabel = l.get from funext he]
  exact congrArg (fun s : List (PositiveCuspidalLabel k) => (s : Multiset (PositiveCuspidalLabel k))) h

section Generic

variable [Finite k]

private theorem gelfandGraevRep_eq (ψ : AddChar k ℂ) (m : ℕ) :
    gelfandGraevRep ψ m = gelfandGraev ψ m := by
  rfl

private theorem gelfandGraev_multiplicity (ψ : AddChar k ℂ) (hψ : ψ ≠ 0) (m : ℕ) :
    (∀ a : IrreducibleClass (GeneralLinear (m + 1) k),
      finrank ℂ (IntertwiningMap (gelfandGraev ψ (m + 1)).ρ (VirtualCharacter.rep a).ρ) ≤ 1) ∧
    Nat.card (ConstituentClass (gelfandGraev ψ (m + 1))) = Nat.card kˣ * Nat.card k ^ m := by
  let : Fintype (GeneralLinear (m + 1) k) := Fintype.ofFinite _
  have hψ' : ψ ≠ 1 := by rwa [AddChar.one_eq_zero]
  obtain ⟨h₁, h₂⟩ := multiplicityFree_of_commuting _ (gelfandGraev_end_mul_comm ψ hψ' m)
  exact ⟨h₁, h₂.trans (gelfandGraev_end_finrank ψ hψ' m)⟩

private theorem finrank_whittaker_cuspidal (ψ : AddChar k ℂ) (hψ : ψ ≠ 0) (hn : 0 < n)
    (a : CuspidalModelClass n k) : finrank ℂ (whittakerVectors (VirtualCharacter.rep a.val).ρ ψ) = 1 := by
  cases n with
  | zero => omega
  | succ n =>
    have h₁ := (gelfandGraev_multiplicity ψ hψ n).1 a.val
    rw [← gelfandGraevRep_eq ψ (n + 1), finrank_intertwiningMap_gelfandGraevRep] at h₁
    have h₂ := a.property.whittakerVectors_ne_bot _ hn
      (FiniteIndexRestriction.exists_ne_zero _ (VirtualCharacter.isIrreducible_rep a.val)) hψ
    have hpos : 0 < finrank ℂ (whittakerVectors (VirtualCharacter.rep a.val).ρ ψ) :=
      Nat.pos_of_ne_zero (fun h => h₂ (Submodule.finrank_eq_zero.mp h))
    exact Nat.le_antisymm h₁ hpos

private theorem gelfandGraev_intertwining_induced_eq_one (ψ : AddChar k ℂ) (hψ : ψ ≠ 0)
    (D : HarishChandraDatum (n + 1) k) :
    finrank ℂ (IntertwiningMap (gelfandGraev ψ (n + 1)).ρ D.induced.ρ) = 1 := by
  rw [← gelfandGraevRep_eq ψ (n + 1), finrank_intertwiningMap_gelfandGraevRep]
  change finrank ℂ (whittakerVectors (harishChandraInduce D.shape
    (externalRep (fun i => VirtualCharacter.rep (D.label i).val))).ρ ψ) = 1
  rw [finrank_whittakerVectors_harishChandraInduce D.shape _ hψ]
  exact Finset.prod_eq_one (fun i _ => finrank_whittaker_cuspidal ψ hψ (D.shape.positive i) (D.label i))

private theorem exists_unique_generic (ψ : AddChar k ℂ) (hψ : ψ ≠ 0) (D : HarishChandraDatum (n + 1) k) :
    ∃! a : ConstituentClass (gelfandGraev ψ (n + 1)), constituentMultiplicity D.induced a.val ≠ 0 := by
  classical
  let G := GeneralLinear (n + 1) k
  let : Fintype G := Fintype.ofFinite G
  let : Fintype (IrreducibleClass G) := Fintype.ofFinite _
  let Γ := gelfandGraev ψ (n + 1)
  let f (a : IrreducibleClass G) := constituentMultiplicity Γ a * constituentMultiplicity D.induced a
  have hs : ∑ a, f a = 1 :=
    (finrank_intertwiningMap_eq_sum_constituentMultiplicity Γ D.induced).symm.trans
      (gelfandGraev_intertwining_induced_eq_one ψ hψ D)
  obtain ⟨a, ha⟩ : ∃ a, f a ≠ 0 := by
    by_contra! h
    rw [Finset.sum_eq_zero (fun a _ => h a)] at hs
    exact zero_ne_one hs
  have hΓ : constituentMultiplicity Γ a ≠ 0 := fun h => ha (by simp [f, h])
  have hD : constituentMultiplicity D.induced a ≠ 0 := fun h => ha (by simp [f, h])
  have haΓ : 0 < finrank ℂ (IntertwiningMap Γ.ρ (VirtualCharacter.rep a).ρ) := by
    rw [finrank_intertwiningMap_symm Γ]
    exact Nat.pos_of_ne_zero hΓ
  refine ⟨⟨a, haΓ⟩, hD, ?_⟩
  intro b hb
  by_contra hne
  have hab : a ≠ b.val := fun h => hne (Subtype.ext h.symm)
  have hbΓ : 0 < constituentMultiplicity Γ b.val := by
    rw [constituentMultiplicity, finrank_intertwiningMap_symm]
    exact b.property
  have hfb : 0 < f b.val := Nat.mul_pos hbΓ (Nat.pos_of_ne_zero hb)
  have hle : (∑ x ∈ ({a, b.val} : Finset (IrreducibleClass G)), f x) ≤ ∑ x, f x :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)
  rw [Finset.sum_pair hab, hs] at hle
  exact (by omega : False)

private def genericDatum {ψ : AddChar k ℂ} (a : ConstituentClass (gelfandGraev ψ n)) :
    HarishChandraDatum n k :=
  (exists_harishChandraDatum (VirtualCharacter.rep a.val) (VirtualCharacter.isIrreducible_rep _)).choose

private theorem genericDatum_multiplicity_ne_zero {ψ : AddChar k ℂ}
    (a : ConstituentClass (gelfandGraev ψ n)) :
    constituentMultiplicity (genericDatum a).induced a.val ≠ 0 := by
  let : Fintype (GeneralLinear n k) := Fintype.ofFinite _
  rw [constituentMultiplicity, finrank_intertwiningMap_symm]
  exact (exists_harishChandraDatum (VirtualCharacter.rep a.val) (VirtualCharacter.isIrreducible_rep _)).choose_spec

/-- Generic irreducible classes correspond to unordered cuspidal labels of the given total rank. -/
def genericClassesEquivCuspidalMultisets (ψ : AddChar k ℂ) (hψ : ψ ≠ 0) (m : ℕ) :
    ConstituentClass (gelfandGraev ψ (m + 1)) ≃ CuspidalMultiset (m + 1) k := by
  let f (a : ConstituentClass (gelfandGraev ψ (m + 1))) : CuspidalMultiset (m + 1) k :=
    ⟨(genericDatum a).labels, (genericDatum a).sum_labelRanks⟩
  apply Equiv.ofBijective f
  constructor
  · intro a b h
    have he : (genericDatum a).labels = (genericDatum b).labels := congrArg Subtype.val h
    have hb : constituentMultiplicity (genericDatum a).induced b.val ≠ 0 := by
      rw [constituentMultiplicity_eq_of_labels_eq _ _ he]
      exact genericDatum_multiplicity_ne_zero b
    obtain ⟨c, _, hc⟩ := exists_unique_generic ψ hψ (genericDatum a)
    exact (hc a (genericDatum_multiplicity_ne_zero a)).trans (hc b hb).symm
  · intro M
    obtain ⟨D, hD⟩ := exists_datum_labels M
    obtain ⟨a, ha, _⟩ := exists_unique_generic ψ hψ D
    refine ⟨a, Subtype.ext ?_⟩
    exact (labels_eq_of_common_constituent (genericDatum a) D a.val
      (genericDatum_multiplicity_ne_zero a) ha).trans hD

/-- The number of cuspidal multisets of positive total rank equals the Gelfand–Graev count. -/
theorem card_cuspidalMultiset_succ (m : ℕ) :
    Nat.card (CuspidalMultiset (m + 1) k) = Nat.card kˣ * Nat.card k ^ m := by
  obtain ⟨ψ, hψ⟩ := (AddChar.exists_apply_ne_zero (α := k) (a := 1)).mpr one_ne_zero
  have hψ' : ψ ≠ 0 := fun h => hψ (by simp [h])
  rw [← Nat.card_congr (genericClassesEquivCuspidalMultisets ψ hψ' m)]
  exact (gelfandGraev_multiplicity ψ hψ' m).2

end Generic

end Langlands.FiniteGeneralLinear
