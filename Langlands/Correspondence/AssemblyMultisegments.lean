import Langlands.Correspondence.AssemblyRelation
import Langlands.Correspondence.ZeroMonodromyExtension
import Langlands.WeilDeligne.DirectSumReindex

/-!
# Multisegment and block-sum combinatorics of the assembly

Unconditional facts about the data of `IsAssembledFrom`: an injective supercuspidal
map makes `segmentOf` injective, so equal multisegments `multisegmentOf` come from
data matched by a permutation of the blocks; matched data have equal block sums; a
surjective supercuspidal map reaches every multisegment; and block sums and
multisegments have rank `∑ (d_i + 1)(m_i + 1)`.
-/

noncomputable section

universe uF uP uA



namespace Langlands.Correspondence

open PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- Equal finite families listed in a multiset agree up to a reindexing. -/
private theorem ofFn_matching {α : Type*} {r s : ℕ} (f : Fin r → α) (g : Fin s → α)
    (h : (List.ofFn f : Multiset α) = List.ofFn g) :
    ∃ e : Fin r ≃ Fin s, ∀ i, f i = g (e i) := by
  classical
  have hp : (List.ofFn f).Perm (List.ofFn g) := Quotient.exact h
  let e₀ : Fin (List.ofFn f).length ≃ Fin (List.ofFn g).length :=
    { toFun := hp.idxBij
      invFun := hp.symm.idxBij
      left_inv := hp.idxBij_symm_leftInverse_idxBij
      right_inv := hp.idxBij_symm_rightInverse_idxBij }
  let e := (finCongr (List.length_ofFn).symm).trans
    (e₀.trans (finCongr List.length_ofFn))
  refine ⟨e, fun i => ?_⟩
  have hi := hp.getElem_idxBij_eq_getElem ((finCongr (List.length_ofFn).symm) i)
  simp only [List.getElem_ofFn] at hi
  exact (congrArg f (Fin.ext rfl)).trans
    (hi.symm.trans (congrArg g (Fin.ext rfl)))

/-- With `c0` injective in every rank, the segment `[c0 σ, ν^m c0 σ]` determines the
rank `d + 1`, the Weil class `σ` and the length `m + 1`. -/
theorem segmentOf_injective {c0 : SupercuspidalMap.{uF, uP, uA} F}
    (hc0 : ∀ n, Function.Injective (c0 n)) {d d' : ℕ}
    {σ : IrreducibleWeilClass.{uF, uP} F d.succPNat}
    {σ' : IrreducibleWeilClass.{uF, uP} F d'.succPNat} {m m' : ℕ}
    (h : segmentOf F c0 σ m = segmentOf F c0 σ' m') :
    (⟨d, σ⟩ : Σ k : ℕ, IrreducibleWeilClass.{uF, uP} F k.succPNat) = ⟨d', σ'⟩ ∧ m = m' := by
  have hb : cuspidalDatumOf F c0 σ = cuspidalDatumOf F c0 σ' := congrArg Segment.base h
  have hm : m + 1 = m' + 1 := congrArg Segment.length h
  obtain rfl : d = d' := Nat.succ_injective (congrArg CuspidalDatum.rank hb)
  obtain rfl : σ = σ' := hc0 _ (eq_of_heq (congr_arg_heq CuspidalDatum.cls hb))
  exact ⟨rfl, Nat.succ_injective hm⟩

/-- With `c0` injective in every rank, equal multisegments `multisegmentOf` come from
block data matched by a bijection of the index sets. -/
theorem multisegmentOf_matching {c0 : SupercuspidalMap.{uF, uP, uA} F}
    (hc0 : ∀ n, Function.Injective (c0 n)) {r r' : ℕ} {d : Fin r → ℕ} {d' : Fin r' → ℕ}
    {σ : ∀ i, IrreducibleWeilClass.{uF, uP} F (d i).succPNat}
    {σ' : ∀ i, IrreducibleWeilClass.{uF, uP} F (d' i).succPNat}
    {m : Fin r → ℕ} {m' : Fin r' → ℕ}
    (h : multisegmentOf F c0 σ m = multisegmentOf F c0 σ' m') :
    ∃ e : Fin r ≃ Fin r', ∀ i,
      (⟨d i, σ i⟩ : Σ k : ℕ, IrreducibleWeilClass.{uF, uP} F k.succPNat) =
          ⟨d' (e i), σ' (e i)⟩ ∧ m i = m' (e i) := by
  obtain ⟨e, he⟩ := ofFn_matching _ _ h
  exact ⟨e, fun i => segmentOf_injective F hc0 (he i)⟩

/-- Equal ranked Weil classes have equal underlying representation classes. -/
theorem weilClassForget_congr
    {x y : Σ k : ℕ, IrreducibleWeilClass.{uF, uP} F k.succPNat} (h : x = y) :
    weilClassForget F x.2 = weilClassForget F y.2 := by
  subst h
  rfl

/-- Block sums of block data matched by a bijection of the index sets are equal. -/
theorem IsBlockSum.eq_of_matching {r r' : ℕ} {d : Fin r → ℕ} {d' : Fin r' → ℕ}
    {σ : ∀ i, IrreducibleWeilClass.{uF, uP} F (d i).succPNat}
    {σ' : ∀ i, IrreducibleWeilClass.{uF, uP} F (d' i).succPNat}
    {m : Fin r → ℕ} {m' : Fin r' → ℕ} {n : ℕ+} {D D' : WeilDeligneClass.{uF, uP} F n}
    (h : IsBlockSum F σ m D) (h' : IsBlockSum F σ' m' D') (e : Fin r ≃ Fin r')
    (he : ∀ i, (⟨d i, σ i⟩ : Σ k : ℕ, IrreducibleWeilClass.{uF, uP} F k.succPNat) =
        ⟨d' (e i), σ' (e i)⟩ ∧ m i = m' (e i)) :
    D = D' := by
  obtain ⟨B, A, hB, hA, ⟨f⟩⟩ := h
  obtain ⟨B', A', hB', hA', ⟨f'⟩⟩ := h'
  have hblock : ∀ i, Nonempty (WeilDeligneRepresentation.Equiv
      (WeilDeligneRepresentation.block (Weil.Local.localNormCharacter F).toMonoidHom
        (B i) (m i + 1))
      (WeilDeligneRepresentation.block (Weil.Local.localNormCharacter F).toMonoidHom
        (B' (e i)) (m' (e i) + 1))) := by
    intro i
    have hcls : FiniteRepresentation.classOf (B i) = FiniteRepresentation.classOf (B' (e i)) :=
      (hB i).trans ((weilClassForget_congr F (he i).1).trans (hB' (e i)).symm)
    rw [← (he i).2]
    exact ⟨WeilDeligneRepresentation.blockEquiv _
      ((FiniteRepresentation.classOf_eq_iff _ _).mp hcls).some _⟩
  let g := WeilDeligneRepresentation.directSumEquiv fun i => (hblock i).some
  let k := WeilDeligneRepresentation.directSumReindexEquiv e fun j =>
    WeilDeligneRepresentation.block (Weil.Local.localNormCharacter F).toMonoidHom
      (B' j) (m' j + 1)
  apply parameterForget_injective (F := F)
  rw [← hA, ← hA']
  exact (WeilDeligneRepresentation.classOf_eq_iff _ _).mpr
    ⟨f.symm.trans (g.trans (k.symm.trans f'))⟩

/-- With `c0` injective in every rank, rank-`n` block sums whose block data have equal
multisegments `multisegmentOf` are equal. -/
theorem IsBlockSum.eq_of_multisegmentOf_eq {c0 : SupercuspidalMap.{uF, uP, uA} F}
    (hc0 : ∀ k, Function.Injective (c0 k)) {r r' : ℕ} {d : Fin r → ℕ} {d' : Fin r' → ℕ}
    {σ : ∀ i, IrreducibleWeilClass.{uF, uP} F (d i).succPNat}
    {σ' : ∀ i, IrreducibleWeilClass.{uF, uP} F (d' i).succPNat}
    {m : Fin r → ℕ} {m' : Fin r' → ℕ} {n : ℕ+} {D D' : WeilDeligneClass.{uF, uP} F n}
    (h : IsBlockSum F σ m D) (h' : IsBlockSum F σ' m' D')
    (he : multisegmentOf F c0 σ m = multisegmentOf F c0 σ' m') :
    D = D' := by
  obtain ⟨e, hm⟩ := multisegmentOf_matching F hc0 he
  exact IsBlockSum.eq_of_matching F h h' e hm

/-- The rank of a block sum is `∑ (d_i + 1)(m_i + 1)`. -/
theorem IsBlockSum.rank_eq {r : ℕ} {d : Fin r → ℕ}
    {σ : ∀ i, IrreducibleWeilClass.{uF, uP} F (d i).succPNat} {m : Fin r → ℕ}
    {n : ℕ+} {D : WeilDeligneClass.{uF, uP} F n} (h : IsBlockSum F σ m D) :
    (n : ℕ) = ∑ i, (d i + 1) * (m i + 1) := by
  obtain ⟨B, A, hB, hA, ⟨f⟩⟩ := h
  have hn : WeilDeligneRepresentation.classRank (parameterForget F D) = n := D.property
  rw [← hn, ← hA]
  change A.rank = _
  have hf : (WeilDeligneRepresentation.directSum fun i =>
      WeilDeligneRepresentation.block (Weil.Local.localNormCharacter F).toMonoidHom
        (B i) (m i + 1)).rank = A.rank :=
    f.representationEquiv.toLinearEquiv.finrank_eq
  rw [← hf, WeilDeligneRepresentation.rank_directSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hr : (B i).rank = d i + 1 :=
    (congrArg FiniteRepresentation.classRank (hB i)).trans (σ i).property
  rw [WeilDeligneRepresentation.rank_block, hr]

/-- The degree of the multisegment `multisegmentOf F c0 σ m` is `∑ (d_i + 1)(m_i + 1)`. -/
theorem degree_multisegmentOf (c0 : SupercuspidalMap.{uF, uP, uA} F) {r : ℕ}
    {d : Fin r → ℕ} (σ : ∀ i, IrreducibleWeilClass.{uF, uP} F (d i).succPNat)
    (m : Fin r → ℕ) :
    (multisegmentOf F c0 σ m).degree = ∑ i, (d i + 1) * (m i + 1) := by
  unfold multisegmentOf Multisegment.degree
  rw [Multiset.map_coe, Multiset.sum_coe, List.map_ofFn, List.sum_ofFn]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Nat.mul_comm _ _

/-- With `c0` surjective in every rank, every segment is a segment `segmentOf`. -/
theorem exists_segmentOf_eq {c0 : SupercuspidalMap.{uF, uP, uA} F}
    (hc0 : ∀ n, Function.Surjective (c0 n))
    (Δ : Segment.{uA, uF} F.canonicalTopologicalData) :
    ∃ (d : ℕ) (σ : IrreducibleWeilClass.{uF, uP} F d.succPNat) (m : ℕ),
      segmentOf F c0 σ m = Δ := by
  obtain ⟨⟨r, hr, a⟩, l, hl⟩ := Δ
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hl.ne'
  obtain ⟨σ, hσ⟩ := hc0 d.succPNat a
  subst hσ
  exact ⟨d, σ, m, rfl⟩

/-- With `c0` surjective in every rank, every multisegment is a multisegment
`multisegmentOf`. -/
theorem exists_multisegmentOf_eq {c0 : SupercuspidalMap.{uF, uP, uA} F}
    (hc0 : ∀ n, Function.Surjective (c0 n))
    (a : Multisegment.{uA, uF} F.canonicalTopologicalData) :
    ∃ (r : ℕ) (d m : Fin r → ℕ) (σ : ∀ i, IrreducibleWeilClass.{uF, uP} F (d i).succPNat),
      multisegmentOf F c0 σ m = a := by
  choose d σ m h using exists_segmentOf_eq F hc0
  refine ⟨a.toList.length, fun i => d (a.toList.get i), fun i => m (a.toList.get i),
    fun i => σ (a.toList.get i), ?_⟩
  unfold multisegmentOf
  simp only [h]
  rw [List.ofFn_get, Multiset.coe_toList]

end Langlands.Correspondence
