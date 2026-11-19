import Langlands.Representation.FiniteGeneralLinear.HarishChandraMackeyMatching

/-! Cuspidal multisets determine the induced multiplicities of finite Harish–Chandra series. -/

noncomputable section

open Module Representation
open scoped BigOperators

namespace Langlands.FiniteGeneralLinear

open FiniteRep GeneralLinear Geometric CuspidalSupport

variable {k : Type*} [Field k] {n : ℕ}

/-- A label-preserving bijection of the blocks of two cuspidal data. -/
abbrev MatchingBlocks (D E : HarishChandraDatum n k) :=
  {e : Fin D.shape.length ≃ Fin E.shape.length // ∀ i, D.blockLabel i = E.blockLabel (e i)}

private theorem labels_eq_of_matchingBlocks {D E : HarishChandraDatum n k}
    (t : MatchingBlocks D E) : D.labels = E.labels := by
  change (Finset.univ.val.map D.blockLabel : Multiset (PositiveCuspidalLabel k)) =
    Finset.univ.val.map E.blockLabel
  calc
    _ = Finset.univ.val.map (fun i => E.blockLabel (t.val i)) :=
      Multiset.map_congr rfl (fun i _ => t.property i)
    _ = (Finset.univ.val.map t.val).map E.blockLabel := by
      simp only [Multiset.map_map, Function.comp_apply]
    _ = _ := congrArg (Multiset.map E.blockLabel) (congrArg Finset.val (Finset.map_univ_equiv t.val))

open Classical in
private theorem card_blockLabel_fiber (D : HarishChandraDatum n k) (a : PositiveCuspidalLabel k) :
    Fintype.card {i : Fin D.shape.length // D.blockLabel i = a} = D.labels.count a := by
  rw [Fintype.card_subtype, HarishChandraDatum.labels, Multiset.count_map, ← Finset.filter_val]
  congr 1
  ext i
  simp [eq_comm]

private def matchingBlocks_of_labels_eq {D E : HarishChandraDatum n k} (h : D.labels = E.labels) :
    MatchingBlocks D E := by
  classical
  let f (a : PositiveCuspidalLabel k) : {i // D.blockLabel i = a} ≃ {j // E.blockLabel j = a} :=
    Fintype.equivOfCardEq (by rw [card_blockLabel_fiber, card_blockLabel_fiber, h])
  exact ⟨Equiv.ofFiberEquiv f, fun i => (Equiv.ofFiberEquiv_map f i).symm⟩

private def matchingBlocksSymm {D E : HarishChandraDatum n k} (t : MatchingBlocks D E) :
    MatchingBlocks E D :=
  ⟨t.val.symm, fun j => by simpa only [Equiv.apply_symm_apply] using (t.property (t.val.symm j)).symm⟩

private def matchingBlocksPostcomp (A : HarishChandraDatum n k) {D E : HarishChandraDatum n k}
    (t : MatchingBlocks D E) : MatchingBlocks A D ≃ MatchingBlocks A E where
  toFun s := ⟨s.val.trans t.val, fun i => (s.property i).trans (t.property (s.val i))⟩
  invFun s := ⟨s.val.trans t.val.symm,
    fun i => (s.property i).trans ((matchingBlocksSymm t).property (s.val i))⟩
  left_inv s := by
    apply Subtype.ext
    apply Equiv.ext
    intro i
    exact t.val.symm_apply_apply (s.val i)
  right_inv s := by
    apply Subtype.ext
    apply Equiv.ext
    intro i
    exact t.val.apply_symm_apply (s.val i)

section Permutations

variable {D E : HarishChandraDatum n k}

private theorem size_eq_of_match (t : MatchingBlocks D E) (i : Fin D.shape.length) :
    D.shape.size i = E.shape.size (t.val i) := congrArg cuspidalLabelRank (t.property i)

private def permutationOfMatch (t : MatchingBlocks D E) : Equiv.Perm (Fin n) :=
  D.shape.indexEquiv.symm.trans ((Equiv.sigmaCongr t.val
    (fun i => finCongr (size_eq_of_match t i))).trans E.shape.indexEquiv)

private theorem permutationOfMatch_index (t : MatchingBlocks D E)
    (i : Fin D.shape.length) (a : Fin (D.shape.size i)) :
    permutationOfMatch t (D.shape.index i a) =
      E.shape.index (t.val i) (Fin.cast (size_eq_of_match t i) a) := by
  unfold permutationOfMatch
  change E.shape.indexEquiv
      (Equiv.sigmaCongr t.val (fun i => finCongr (size_eq_of_match t i))
        (D.shape.indexEquiv.symm (D.shape.indexEquiv ⟨i, a⟩))) = _
  rw [Equiv.symm_apply_apply]
  rfl

private theorem permutationOfMatch_minimal (t : MatchingBlocks D E) :
    IsMinimalRepresentative D.shape E.shape (permutationOfMatch t) := by
  constructor
  · intro i a b hab
    change permutationOfMatch t (D.shape.index i a) < permutationOfMatch t (D.shape.index i b)
    rw [permutationOfMatch_index, permutationOfMatch_index]
    exact index_strictMono E.shape _ (Fin.cast_strictMono _ hab)
  · intro j
    obtain ⟨i, rfl⟩ := t.val.surjective j
    have he (a : Fin (E.shape.size (t.val i))) :
        (permutationOfMatch t).symm (E.shape.index (t.val i) a) =
          D.shape.index i (Fin.cast (size_eq_of_match t i).symm a) := by
      apply (permutationOfMatch t).injective
      rw [Equiv.apply_symm_apply, permutationOfMatch_index]
      simp
    intro a b hab
    change (permutationOfMatch t).symm (E.shape.index (t.val i) a) <
      (permutationOfMatch t).symm (E.shape.index (t.val i) b)
    rw [he, he]
    exact index_strictMono D.shape _ (Fin.cast_strictMono _ hab)

private theorem permutationOfMatch_conjugatesLevi (t : MatchingBlocks D E) :
    ConjugatesLevi (F := k) D.shape E.shape (permutationOfMatch t) := by
  apply conjugatesLevi_of_blockIndex _ (fun i => (t.val i).val)
    (Fin.val_injective.comp t.val.injective)
  intro a
  obtain ⟨⟨i, b⟩, rfl⟩ := D.shape.indexEquiv.surjective a
  change (blockIndex E.shape (permutationOfMatch t (D.shape.index i b))).val =
    (t.val (blockIndex D.shape (D.shape.index i b))).val
  rw [permutationOfMatch_index, blockIndex_index, blockIndex_index]

private abbrev MatchingRepresentative (D E : HarishChandraDatum n k) :=
  {w : MinimalRepresentatives D.shape E.shape //
    ∃ hW : ConjugatesLevi (F := k) D.shape E.shape w.val,
      ∀ i, D.blockLabel i = E.blockLabel (blockEquiv hW i)}

private def matchingRepresentativeEquiv (D E : HarishChandraDatum n k) :
    MatchingRepresentative D E ≃ MatchingBlocks D E := by
  let f (r : MatchingRepresentative D E) : MatchingBlocks D E :=
    ⟨blockEquiv r.property.choose, r.property.choose_spec⟩
  apply Equiv.ofBijective f
  constructor
  · intro r s hrs
    apply Subtype.ext
    apply Subtype.ext
    apply Equiv.ext
    intro j
    obtain ⟨⟨i, a⟩, rfl⟩ := D.shape.indexEquiv.surjective j
    change r.val.val (D.shape.index i a) = s.val.val (D.shape.index i a)
    rw [apply_index_eq r.val.property r.property.choose, apply_index_eq s.val.property s.property.choose]
    have he := congrArg (fun b : MatchingBlocks D E => b.val i) hrs
    change blockMap D.shape E.shape r.val.val i = blockMap D.shape E.shape s.val.val i at he
    apply congrArg E.shape.indexEquiv
    refine Sigma.ext (x := ⟨_, _⟩) (y := ⟨_, _⟩) he ?_
    exact (Fin.heq_ext_iff (congrArg E.shape.size he)).mpr rfl
  · intro t
    let w : MinimalRepresentatives D.shape E.shape := ⟨permutationOfMatch t, permutationOfMatch_minimal t⟩
    have hW := permutationOfMatch_conjugatesLevi t
    have he (i : Fin D.shape.length) : blockEquiv hW i = t.val i := by
      change blockIndex E.shape (permutationOfMatch t (D.shape.index i ⟨0, D.shape.positive i⟩)) = _
      rw [permutationOfMatch_index, blockIndex_index]
    let r : MatchingRepresentative D E := ⟨w, hW, fun i => by rw [he]; exact t.property i⟩
    refine ⟨r, Subtype.ext (Equiv.ext fun i => ?_)⟩
    exact he i

end Permutations

section Induction

variable [Finite k]

/-- The intertwining dimension between two induced cuspidal data counts matching block bijections. -/
theorem finrank_intertwiningMap_induced_eq_card_matchingBlocks (D E : HarishChandraDatum n k) :
    finrank ℂ (IntertwiningMap D.induced.ρ E.induced.ρ) = Nat.card (MatchingBlocks D E) := by
  classical
  let := Fintype.ofFinite (GeneralLinear n k)
  let I := MinimalRepresentatives D.shape E.shape
  let : Fintype I := Fintype.ofFinite I
  change finrank ℂ (IntertwiningMap
    (induceRep (D.shape.parabolic k) (pullbackRep (D.shape.leviProjection k) D.leviRep)).ρ
    (induceRep (E.shape.parabolic k) (pullbackRep (E.shape.leviProjection k) E.leviRep)).ρ) = _
  rw [finrank_intertwiningMap_induceRep _ _ _ _ (fun w : I => (permutation n k w.val)⁻¹)
    (parabolicDoubleCoset_bijective D.shape E.shape)]
  change (∑ w : I, harishChandraMackeyTerm D E w) = _
  let q (w : I) : Prop := ∃ hW : ConjugatesLevi (F := k) D.shape E.shape w.val,
    ∀ i, D.blockLabel i = E.blockLabel (blockEquiv hW i)
  let : DecidablePred q := Classical.decPred q
  have hq (w : I) : harishChandraMackeyTerm D E w = if q w then 1 else 0 := by
    by_cases hW : ConjugatesLevi (F := k) D.shape E.shape w.val
    · have hw : q w ↔ ∀ i, D.blockLabel i = E.blockLabel (blockEquiv hW i) :=
        ⟨fun ⟨_, hp⟩ => hp, fun hp => ⟨hW, hp⟩⟩
      rw [if_congr hw rfl rfl]
      exact harishChandraMackeyTerm_eq_ite D E w hW
    · have hnq : ¬q w := fun ⟨hw, _⟩ => hW hw
      rw [ite_eq_right hnq]
      exact not_ne_iff.mp (fun hr => hW (conjugatesLevi_of_mackeyTerm_ne_zero D E w hr))
  simp_rw [hq, Finset.sum_boole]
  rw [← Nat.card_congr (matchingRepresentativeEquiv D E)]
  change _ = Nat.card {w : I // q w}
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

/-- A common irreducible constituent forces equality of the cuspidal label multisets. -/
theorem labels_eq_of_common_constituent (D E : HarishChandraDatum n k)
    (a : IrreducibleClass (GeneralLinear n k)) (hD : constituentMultiplicity D.induced a ≠ 0)
    (hE : constituentMultiplicity E.induced a ≠ 0) : D.labels = E.labels := by
  classical
  let := Fintype.ofFinite (GeneralLinear n k)
  let := Fintype.ofFinite (IrreducibleClass (GeneralLinear n k))
  have hpos : 0 < finrank ℂ (IntertwiningMap D.induced.ρ E.induced.ρ) := by
    rw [finrank_intertwiningMap_eq_sum_constituentMultiplicity]
    exact lt_of_lt_of_le (Nat.mul_pos (Nat.pos_of_ne_zero hD) (Nat.pos_of_ne_zero hE))
      (Finset.single_le_sum
        (f := fun b => constituentMultiplicity D.induced b * constituentMultiplicity E.induced b)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ a))
  rw [finrank_intertwiningMap_induced_eq_card_matchingBlocks] at hpos
  obtain ⟨⟨t⟩, _⟩ := Nat.card_pos_iff.mp hpos
  exact labels_eq_of_matchingBlocks t

/-- Reordering the cuspidal factors preserves every induced constituent multiplicity. -/
theorem constituentMultiplicity_eq_of_labels_eq (D E : HarishChandraDatum n k)
    (h : D.labels = E.labels) (a : IrreducibleClass (GeneralLinear n k)) :
    constituentMultiplicity D.induced a = constituentMultiplicity E.induced a := by
  classical
  let := Fintype.ofFinite (GeneralLinear n k)
  let := Fintype.ofFinite (IrreducibleClass (GeneralLinear n k))
  let t := matchingBlocks_of_labels_eq h
  have hDD : finrank ℂ (IntertwiningMap D.induced.ρ D.induced.ρ) =
      finrank ℂ (IntertwiningMap D.induced.ρ E.induced.ρ) := by
    rw [finrank_intertwiningMap_induced_eq_card_matchingBlocks,
      finrank_intertwiningMap_induced_eq_card_matchingBlocks]
    exact Nat.card_congr (matchingBlocksPostcomp D t)
  have hEE : finrank ℂ (IntertwiningMap E.induced.ρ E.induced.ρ) =
      finrank ℂ (IntertwiningMap D.induced.ρ E.induced.ρ) := by
    rw [finrank_intertwiningMap_symm D.induced E.induced,
      finrank_intertwiningMap_induced_eq_card_matchingBlocks,
      finrank_intertwiningMap_induced_eq_card_matchingBlocks]
    exact Nat.card_congr (matchingBlocksPostcomp E (matchingBlocksSymm t))
  simp only [finrank_intertwiningMap_eq_sum_constituentMultiplicity] at hDD hEE
  let f (b : IrreducibleClass (GeneralLinear n k)) : ℤ := constituentMultiplicity D.induced b
  let g (b : IrreducibleClass (GeneralLinear n k)) : ℤ := constituentMultiplicity E.induced b
  have hD : ∑ b, f b * f b = ∑ b, f b * g b := by
    dsimp only [f, g]
    exact_mod_cast hDD
  have hE : ∑ b, g b * g b = ∑ b, f b * g b := by
    dsimp only [f, g]
    exact_mod_cast hEE
  have hz : ∑ b, (f b - g b)^2 = 0 := by
    calc
      _ = ∑ b, (f b * f b + g b * g b - 2 * (f b * g b)) := by
        apply Finset.sum_congr rfl
        intro b _
        ring
      _ = _ := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hD, hE]
        ring
  have ha := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => sq_nonneg (f b - g b))).mp hz a
    (Finset.mem_univ _)
  have he : f a = g a := sub_eq_zero.mp (sq_eq_zero_iff.mp ha)
  exact Int.ofNat.inj he

end Induction

end Langlands.FiniteGeneralLinear
