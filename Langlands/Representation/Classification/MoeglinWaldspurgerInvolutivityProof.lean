import Langlands.Representation.Classification.MoeglinWaldspurgerStatements
import Langlands.Representation.Classification.MoeglinWaldspurgerKnuthSystem

/-!
# Involutivity of the Moeglin–Waldspurger recursion

The proof is a simultaneous strong induction on a weight `N` of two statements about
row insertion (`PStmt` and `GStmt`).  `PStmt w` says that the first round of `dual w`
emits a longest interval `S` of `w` with the greatest ending and leaves
`dual (w.erase S)`; with the bridge `dual a = emit e n + dual (insR a e (e+1)).1`
this gives `dual (dual w) = w`.
-/

namespace Langlands.MoeglinWaldspurger.Involution

open Row (Desc KP)

/-- The induction statement `P`: for an interval `S` of `w` with the greatest ending `e`
and the least beginning among the intervals ending at `e`, the first round of `dual w`
(the insertion of `e + 1` at row `e`) returns `dual (w.erase S)` and bumps `S.length`
times. -/
def PStmt (w : Multisegment) : Prop :=
  ∀ (e : ℤ) (S : Interval), (∀ J ∈ w, J.ending ≤ e) → S ∈ w → S.ending = e →
    (∀ I ∈ w, I.ending = e → S.beginning ≤ I.beginning) →
    insR (dual w) e (e + 1) = (dual (w.erase S), S.length)

/-- The induction statement `G`: inserting `v` at row `f` into `y` and then inserting
`f + 1 - n` (with `n` the bump count) at row `f` into the dual undoes the first
insertion on the dual side. -/
def GStmt (y : Multisegment) (f v : ℤ) : Prop :=
  (∀ J ∈ y, J.ending ≤ f) → v ≤ f + 1 →
    insR (dual (insR y f v).1) f (f + 1 - (insR y f v).2) = (dual y, (f + 1 - v).toNat)

/-! ## Auxiliary facts -/

theorem pick_some_of_mem {a : Multisegment} {g v : ℤ} {J : Interval} (hJ : J ∈ a)
    (hJg : J.ending = g) (hJv : J.beginning < v) : ∃ I, pick a g v = some I := by
  cases hp : pick a g v with
  | none =>
    rcases (pick_none_iff a g v).mp hp J hJ with h | h
    · exact absurd hJg h
    · exact absurd hJv (not_lt.mpr h)
  | some I => exact ⟨I, rfl⟩

theorem pick_some_of_count_pos {a : Multisegment} {g v : ℤ} (h : 0 < (insR a g v).2) :
    ∃ I, pick a g v = some I := by
  cases hp : pick a g v with
  | none =>
    rw [insR_of_pick_none hp] at h
    exact absurd h (lt_irrefl 0)
  | some I => exact ⟨I, rfl⟩

theorem count_pos_of_pick {a : Multisegment} {g v : ℤ} {I : Interval}
    (h : pick a g v = some I) : 0 < (insR a g v).2 := by
  rw [insR_of_pick_some h]
  exact Nat.succ_pos _

/-- An interval at the insertion row after an insertion is an old interval or the new one. -/
theorem mem_insR_top {a : Multisegment} {g v : ℤ} (ha : ∀ J ∈ a, J.ending ≤ g) {J : Interval}
    (hJ : J ∈ (insR a g v).1) (hJg : J.ending = g) : J ∈ a ∨ J.beginning = v := by
  have hpart := chain_partition a g v
  simp only [insR] at hJ
  rcases Multiset.mem_add.mp hJ with hJ | hJ
  · rcases Multiset.mem_add.mp hJ with hJ | hJ
    · left
      rw [← hpart]
      exact Multiset.mem_add.mpr (Or.inr hJ)
    · obtain ⟨I, hI, -, hIe⟩ := mem_shorten hJ
      have hIa : I ∈ a := by
        rw [← hpart]
        exact Multiset.mem_add.mpr (Or.inl hI)
      have := ha I hIa
      omega
  · exact Or.inr (mem_seg.mp hJ).1

theorem weight_singleton (S : Interval) : weight {S} = S.length := by
  simp [weight]

theorem weight_place_coe (C : List ℤ) (g : ℤ) :
    weight (place ↑C g) = (C.map fun b => (g + 1 - b).toNat).sum := by
  induction C with
  | nil => simp
  | cons c C ih =>
    rw [← Multiset.cons_coe, place_cons, weight_add, weight_seg, ih, List.map_cons,
      List.sum_cons]

theorem sum_toNat_le (C : List ℤ) (f : ℤ) :
    (C.map fun c => (f - c).toNat).sum ≤ (C.map fun c => (f + 1 - c).toNat).sum := by
  induction C with
  | nil => simp
  | cons c C ih =>
    simp only [List.map_cons, List.sum_cons]
    omega

/-- A weakly decreasing list with an entry `< v` splits at its first entry `< v`. -/
theorem exists_split (C : List ℤ) (v : ℤ) (h : ∃ c ∈ C, c < v) :
    ∃ (P : List ℤ) (d : ℤ) (Q : List ℤ), C = P ++ d :: Q ∧ (∀ x ∈ P, v ≤ x) ∧ d < v := by
  induction C with
  | nil => simp at h
  | cons c C ih =>
    by_cases hc : c < v
    · exact ⟨[], c, C, rfl, by simp, hc⟩
    · obtain ⟨x, hx, hxv⟩ := h
      rcases List.mem_cons.mp hx with rfl | hx
      · exact absurd hxv hc
      · obtain ⟨P, d, Q, hC, hP, hd⟩ := ih ⟨x, hx, hxv⟩
        refine ⟨c :: P, d, Q, by rw [hC]; rfl, ?_, hd⟩
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact not_lt.mp hc
        · exact hP y hy

/-! ## The cases of `P` -/

/-- `P` when `S` is the only interval with the greatest ending: reduction to `G`. -/
theorem p_unique {y : Multisegment} {e : ℤ} {S : Interval} (hSe : S.ending = e)
    (hy : ∀ J ∈ y, J.ending ≤ e - 1) (hG : GStmt y (e - 1) S.beginning) :
    insR (dual (y + {S})) e (e + 1) = (dual y, S.length) := by
  have hSb : S.beginning ≤ e := hSe ▸ S.nonempty
  have hy' : ∀ J ∈ y, J.ending < e := fun J hJ => by have := hy J hJ; omega
  have hw : y + {S} = place {S.beginning} e + y := by
    rw [place_singleton, ← hSe, seg_self, add_comm]
  have hwe : ∀ J ∈ y + {S}, J.ending ≤ e := by
    intro J hJ
    rcases Multiset.mem_add.mp hJ with hJ | hJ
    · have := hy J hJ
      omega
    · rw [Multiset.mem_singleton.mp hJ, hSe]
  have hround : insR (y + {S}) e (e + 1) =
      ((insR y (e - 1) S.beginning).1, (insR y (e - 1) S.beginning).2 + 1) := by
    rw [hw, rd1_some (M := {S.beginning}) (z' := y) (g := e) (v := e + 1) (m := S.beginning)
      (Multiset.mem_singleton_self _) (by omega)
      (fun x hx _ => le_of_eq (Multiset.mem_singleton.mp hx)) (by omega) hy',
      Multiset.erase_singleton, zero_add, place_singleton, seg_of_lt (by omega : e < e + 1),
      add_zero]
  have hG' := hG hy (by omega)
  have hxe := insR_endings y (e - 1) S.beginning (e - 1) hy le_rfl
  obtain ⟨⟨x, r⟩, hxr⟩ : ∃ p, insR y (e - 1) S.beginning = p := ⟨_, rfl⟩
  rw [hxr] at hround hG' hxe
  dsimp only at hround hG' hxe
  simp only [sub_add_cancel] at hG'
  have hdxe : ∀ J ∈ dual x, J.ending < e := fun J hJ => by
    have := dual_endings x (e - 1) hxe J hJ
    omega
  have hdw : dual (y + {S}) = place {e - (r : ℤ)} e + dual x := by
    rw [bridge hwe, hround, emit, place_singleton]
    dsimp only
    rw [show e + 1 - ((r + 1 : ℕ) : ℤ) = e - (r : ℤ) by push_cast; ring]
  rw [hdw, rd1_some (M := {e - (r : ℤ)}) (z' := dual x) (g := e) (v := e + 1) (m := e - (r : ℤ))
      (Multiset.mem_singleton_self _) (by omega)
      (fun x hx _ => le_of_eq (Multiset.mem_singleton.mp hx)) (by omega) hdxe,
    Multiset.erase_singleton, zero_add, place_singleton, seg_of_lt (by omega : e < e + 1),
    add_zero, hG']
  simp only [Interval.length, hSe]

/-- `P` when another interval has the greatest ending: reduction to `P` for the residual
of the first round plus `S`. -/
theorem p_two {w' : Multisegment} {e : ℤ} {S : Interval} (hw' : ∀ J ∈ w', J.ending ≤ e)
    (hSe : S.ending = e) (hSmin : ∀ I ∈ w', I.ending = e → S.beginning ≤ I.beginning)
    {J : Interval} (hJ : J ∈ w') (hJe : J.ending = e)
    (hP : PStmt ((insR w' e (e + 1)).1 + {S})) :
    insR (dual (w' + {S})) e (e + 1) = (dual w', S.length) := by
  obtain ⟨I, hI⟩ := pick_some_of_mem (v := e + 1) hJ hJe (by have := J.nonempty; omega)
  have hIe := (pick_spec hI).1
  have hSI : S.beginning ≤ I.beginning := hSmin I (pick_mem hI) hIe
  have hadd := insR_add_of_pick hI hSe hSI
  have hn := count_pos_of_pick hI
  have hwe : ∀ K ∈ w' + {S}, K.ending ≤ e := by
    intro K hK
    rcases Multiset.mem_add.mp hK with hK | hK
    · exact hw' K hK
    · rw [Multiset.mem_singleton.mp hK, hSe]
  have hmono := mono (w' + {S}) e hwe
  rw [hadd] at hmono
  have hxe := insR_endings w' e (e + 1) e hw' le_rfl
  have hbridge := bridge hw'
  have htop : ∀ K ∈ (insR w' e (e + 1)).1, K.ending = e → K ∈ w' ∨ K.beginning = e + 1 :=
    fun K hK hKe => mem_insR_top hw' hK hKe
  obtain ⟨⟨x, n⟩, hxn⟩ : ∃ p, insR w' e (e + 1) = p := ⟨_, rfl⟩
  rw [hxn] at hadd hmono hn hP hxe hbridge htop
  dsimp only at hadd hmono hn hP hxe hbridge htop
  have hP' := hP e S
    (by
      intro K hK
      rcases Multiset.mem_add.mp hK with hK | hK
      · exact hxe K hK
      · rw [Multiset.mem_singleton.mp hK, hSe])
    (Multiset.mem_add.mpr (Or.inr (Multiset.mem_singleton_self _))) hSe
    (by
      intro K hK hKe
      rcases Multiset.mem_add.mp hK with hK | hK
      · rcases htop K hK hKe with h | h
        · exact hSmin K h hKe
        · rw [h]
          have := S.nonempty
          omega
      · rw [Multiset.mem_singleton.mp hK])
  rw [Multiset.erase_add_right_pos _ (Multiset.mem_singleton_self S), Multiset.erase_singleton,
    add_zero] at hP'
  have hcount : 0 < (insR (dual (x + {S})) e (e + 1)).2 := by
    rw [hP']
    exact S.length_pos
  obtain ⟨I', hI'⟩ := pick_some_of_count_pos hcount
  have hle : e + 1 - (n : ℤ) ≤ I'.beginning := hmono I' (pick_mem hI') (pick_spec hI').1
  have hJdef : emit e n = {(⟨e + 1 - (n : ℤ), e, by omega⟩ : Interval)} :=
    seg_of_le (by omega)
  have hins := insR_add_of_pick (J := ⟨e + 1 - (n : ℤ), e, by omega⟩) hI' rfl hle
  rw [bridge hwe, hadd, hbridge, hJdef, add_comm _ (dual (x + {S})), hins, hP']
  dsimp only
  rw [add_comm]

/-! ## The cases of `G` -/

/-- `G` for `v = f + 1`: the insertion is a round, and the emitted interval goes back. -/
theorem g_top {y : Multisegment} {f : ℤ} (hy : ∀ J ∈ y, J.ending ≤ f) :
    insR (dual (insR y f (f + 1)).1) f (f + 1 - (insR y f (f + 1)).2) =
      (dual y, (f + 1 - (f + 1)).toNat) := by
  have hm := mono y f hy
  have hpn : pick (dual (insR y f (f + 1)).1) f (f + 1 - (insR y f (f + 1)).2) = none := by
    rw [pick_none_iff]
    intro I hI
    by_cases hIe : I.ending = f
    · exact Or.inr (hm I hI hIe)
    · exact Or.inl hIe
  rw [insR_of_pick_none hpn, bridge hy, emit, sub_self, Int.toNat_zero]
  exact Prod.ext (add_comm _ _) rfl

/-- `G` when no entry of row `f` is below `v`: reduction to `P`. -/
theorem g_none {C : List ℤ} {z : Multisegment} {f v : ℤ}
    (hz : ∀ J ∈ z, J.ending ≤ f - 1) (hall : ∀ c ∈ C, v ≤ c) (hvf : v ≤ f)
    (hP : PStmt (place (↑C + {v}) f + z)) :
    insR (dual (insR (place ↑C f + z) f v).1) f (f + 1 - (insR (place ↑C f + z) f v).2) =
      (dual (place ↑C f + z), (f + 1 - v).toNat) := by
  have hz' : ∀ J ∈ z, J.ending < f := fun J hJ => by have := hz J hJ; omega
  rw [rd1_none (fun x hx => hall x (Multiset.mem_coe.mp hx)) hz']
  dsimp only
  rw [Nat.cast_zero, sub_zero]
  have hvM : v ∈ (↑C + {v} : Multiset ℤ) :=
    Multiset.mem_add.mpr (Or.inr (Multiset.mem_singleton_self v))
  have hS : (⟨v, f, hvf⟩ : Interval) ∈ place (↑C + {v}) f + z :=
    Multiset.mem_add.mpr (Or.inl (mem_place.mpr ⟨hvM, rfl⟩))
  have hxe : ∀ J ∈ place (↑C + {v}) f + z, J.ending ≤ f := by
    intro J hJ
    rcases Multiset.mem_add.mp hJ with hJ | hJ
    · exact (mem_place.mp hJ).2.le
    · exact (hz' J hJ).le
  have hmin : ∀ I ∈ place (↑C + {v}) f + z, I.ending = f → v ≤ I.beginning := by
    intro I hI hIe
    rcases Multiset.mem_add.mp hI with hI | hI
    · rcases Multiset.mem_add.mp (mem_place.mp hI).1 with h | h
      · exact hall _ (Multiset.mem_coe.mp h)
      · rw [Multiset.mem_singleton.mp h]
    · have := hz' I hI
      omega
  rw [hP f ⟨v, f, hvf⟩ hxe hS rfl hmin, Multiset.erase_add_left_pos z
      (show (⟨v, f, hvf⟩ : Interval) ∈ place (↑C + {v}) f from mem_place.mpr ⟨hvM, rfl⟩),
    place_erase hvM hvf, Multiset.erase_add_right_pos _ (Multiset.mem_singleton_self v),
    Multiset.erase_singleton, add_zero]
  simp only [Interval.length, Prod.mk.injEq, true_and]
  omega

/-- `G` when the insertion bumps an entry of row `f` (Case II): the system lemma and `G`
one row lower. -/
theorem g_bump {P Q : List ℤ} {z : Multisegment} {f v d : ℤ}
    (hdesc : Desc (P ++ d :: Q)) (hCf : ∀ c ∈ P ++ d :: Q, c ≤ f)
    (hz : ∀ J ∈ z, J.ending ≤ f - 1) (hPv : ∀ x ∈ P, v ≤ x) (hdv : d < v) (hvf : v ≤ f)
    (hG : GStmt (insW z (f - 1) (P ++ d :: Q)).1 (f - 1) v) :
    insR (dual (insR (place ↑(P ++ d :: Q) f + z) f v).1) f
        (f + 1 - (insR (place ↑(P ++ d :: Q) f + z) f v).2) =
      (dual (place ↑(P ++ d :: Q) f + z), (f + 1 - v).toNat) := by
  have hz' : ∀ J ∈ z, J.ending < f := fun J hJ => by have := hz J hJ; omega
  have hQd : ∀ x ∈ Q, x ≤ d := fun x hx =>
    (List.pairwise_cons.mp (List.pairwise_append.mp hdesc).2.1).1 x hx
  have hdP : d ∉ P := fun h => by have := hPv d h; omega
  -- the bump at row `f`
  have hmax : ∀ x ∈ (↑(P ++ d :: Q) : Multiset ℤ), x < v → x ≤ d := by
    intro x hx hxv
    rcases List.mem_append.mp (Multiset.mem_coe.mp hx) with hx | hx
    · have := hPv x hx
      omega
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact le_rfl
      · exact hQd x hx
  have hround := rd1_some (M := ↑(P ++ d :: Q)) (z' := z) (g := f) (v := v) (m := d)
    (Multiset.mem_coe.mpr (by simp)) hdv hmax (by omega) hz'
  have hrow : (↑(P ++ d :: Q) : Multiset ℤ).erase d + {v} = ↑(P ++ v :: Q) := by
    rw [Multiset.coe_erase, List.erase_append_right _ hdP, List.erase_cons_head, add_comm,
      Multiset.singleton_add, Multiset.cons_coe, Multiset.coe_eq_coe]
    exact List.perm_middle.symm
  rw [hrow] at hround
  -- the new top row `P ++ v :: Q`
  have hC'd : Desc (P ++ v :: Q) := by
    have hPd := (List.pairwise_append.mp hdesc).1
    have hQ := (List.pairwise_cons.mp (List.pairwise_append.mp hdesc).2.1).2
    have hPdQ := (List.pairwise_append.mp hdesc).2.2
    refine List.pairwise_append.mpr ⟨hPd, List.pairwise_cons.mpr ⟨fun x hx => ?_, hQ⟩,
      fun a ha b hb => ?_⟩
    · have := hQd x hx
      omega
    · rcases List.mem_cons.mp hb with rfl | hb
      · exact hPv a ha
      · exact hPdQ a ha b (List.mem_cons_of_mem _ hb)
  have hC'f : ∀ x ∈ P ++ v :: Q, x ≤ f := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hCf x (List.mem_append_left _ hx)
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact hvf
      · exact hCf x (List.mem_append_right _ (List.mem_cons_of_mem _ hx))
  -- the system lemma one row lower
  have hlet : ∀ x ∈ P ++ d :: Q ++ [v], x ≤ f - 1 + 1 := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · have := hCf x hx
      omega
    · rw [List.mem_singleton.mp hx]
      omega
  obtain ⟨hfin, ρ, t, r'', s, hρ, hs, hcf⟩ := system z (f - 1) P Q d v hz ⟨hdesc, hPv, hdv⟩ hlet
  have hZ1e := insR_endings z (f - 1) d (f - 1) hz le_rfl
  obtain ⟨⟨Z1, r'⟩, hZr⟩ : ∃ p, insR z (f - 1) d = p := ⟨_, rfl⟩
  rw [hZr] at hround hZ1e
  dsimp only at hround hZ1e
  have e1 : insW z (f - 1) (P ++ d :: Q ++ [v]) =
      ((insR (insW z (f - 1) (P ++ d :: Q)).1 (f - 1) v).1,
        (insW z (f - 1) (P ++ d :: Q)).2 ++ [(insR (insW z (f - 1) (P ++ d :: Q)).1 (f - 1) v).2]) := by
    rw [insW_append]
    simp [insW_cons]
  have e2 : insW z (f - 1) (d :: (P ++ v :: Q)) =
      ((insW Z1 (f - 1) (P ++ v :: Q)).1, r' :: (insW Z1 (f - 1) (P ++ v :: Q)).2) := by
    rw [insW_cons, hZr]
  rw [e1, e2] at hfin
  rw [e1] at hρ
  rw [e2] at hs
  dsimp only at hfin hρ hs
  obtain ⟨hρ1, hρ2⟩ := List.append_inj' hρ rfl
  have ht : (insR (insW z (f - 1) (P ++ d :: Q)).1 (f - 1) v).2 = t := by simpa using hρ2
  obtain ⟨hr', hs'⟩ := List.cons.inj hs
  subst hρ1 ht hr' hs'
  -- `G` one row lower
  have hZye := insW_endings (P ++ d :: Q) z (f - 1) (f - 1) hz le_rfl
  have hG' := hG hZye (by omega)
  rw [hfin] at hG'
  simp only [sub_add_cancel] at hG'
  have hZxe := insW_endings (P ++ v :: Q) Z1 (f - 1) (f - 1) hZ1e le_rfl
  have hdZx : ∀ J ∈ dual (insW Z1 (f - 1) (P ++ v :: Q)).1, J.ending < f := fun J hJ => by
    have := dual_endings _ (f - 1) hZxe J hJ
    omega
  -- rewrite both duals by row processing
  rw [hround]
  dsimp only
  rw [add_comm Z1, rowProc (P ++ v :: Q) f Z1 hC'd hC'f hZ1e, rowProc (P ++ d :: Q) f z hdesc hCf hz,
    show f + 1 - ((r' + 1 : ℕ) : ℤ) = f - (r' : ℤ) by push_cast; ring]
  -- the count fact
  obtain ⟨hcf1, hcf2, hcf3⟩ := hcf
  have hts : (insR (insW z (f - 1) (P ++ d :: Q)).1 (f - 1) v).2 ∈
      (insW Z1 (f - 1) (P ++ v :: Q)).2 := by
    have h1 : (insR (insW z (f - 1) (P ++ d :: Q)).1 (f - 1) v).2 ∈
        (↑(insW Z1 (f - 1) (P ++ v :: Q)).2 : Multiset ℕ) + {r'} := by
      rw [hcf1]
      exact Multiset.mem_add.mpr (Or.inr (Multiset.mem_singleton_self _))
    rcases Multiset.mem_add.mp h1 with h | h
    · exact Multiset.mem_coe.mp h
    · rw [Multiset.mem_singleton.mp h] at hcf2
      exact absurd hcf2 (lt_irrefl _)
  rw [rd1_some (M := ↑((insW Z1 (f - 1) (P ++ v :: Q)).2.map (fun r : ℕ => f - (r : ℤ))))
      (z' := dual (insW Z1 (f - 1) (P ++ v :: Q)).1) (g := f) (v := f - (r' : ℤ))
      (m := f - ((insR (insW z (f - 1) (P ++ d :: Q)).1 (f - 1) v).2 : ℤ))
      (Multiset.mem_coe.mpr (List.mem_map.mpr ⟨_, hts, rfl⟩)) (by omega)
      (fun x hx hxr => by
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp hx)
        have := hcf3 a ha (by omega)
        omega)
      (by omega) hdZx, hG']
  have hφ : Function.Injective (fun r : ℕ => f - (r : ℤ)) := fun a b h => by
    simpa using h
  have hM : (↑(insW Z1 (f - 1) (P ++ v :: Q)).2 : Multiset ℕ).erase
      (insR (insW z (f - 1) (P ++ d :: Q)).1 (f - 1) v).2 + {r'} =
      ↑(insW z (f - 1) (P ++ d :: Q)).2 := by
    rw [← Multiset.erase_add_left_pos _ (Multiset.mem_coe.mpr hts), hcf1,
      Multiset.erase_add_right_pos _ (Multiset.mem_singleton_self _), Multiset.erase_singleton,
      add_zero]
  have hM' := congrArg (Multiset.map (fun r : ℕ => f - (r : ℤ))) hM
  rw [Multiset.map_add, Multiset.map_erase _ hφ, Multiset.map_singleton, Multiset.map_coe,
    Multiset.map_coe] at hM'
  rw [hM']
  dsimp only
  refine Prod.ext (add_comm _ _) ?_
  dsimp only
  omega

/-! ## The induction -/

theorem main (N : ℕ) : (∀ w, weight w = N → PStmt w) ∧
    (∀ y f v, weight y + (f + 1 - v).toNat = N → GStmt y f v) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  have hP : ∀ w, weight w = N → PStmt w := by
    intro w hwN e S hw hS hSe hSmin
    obtain ⟨w', rfl⟩ : ∃ w', w = w' + {S} :=
      ⟨w.erase S, by rw [add_comm, Multiset.singleton_add, Multiset.cons_erase hS]⟩
    rw [Multiset.erase_add_right_pos _ (Multiset.mem_singleton_self S), Multiset.erase_singleton,
      add_zero]
    have hw' : ∀ J ∈ w', J.ending ≤ e := fun J hJ => hw J (Multiset.mem_add.mpr (Or.inl hJ))
    have hSmin' : ∀ I ∈ w', I.ending = e → S.beginning ≤ I.beginning :=
      fun I hI => hSmin I (Multiset.mem_add.mpr (Or.inl hI))
    rw [weight_add, weight_singleton] at hwN
    by_cases htwo : ∃ J ∈ w', J.ending = e
    · obtain ⟨J, hJ, hJe⟩ := htwo
      refine p_two hw' hSe hSmin' hJ hJe ((ih _ ?_).1 _ rfl)
      obtain ⟨I, hI⟩ := pick_some_of_mem (v := e + 1) hJ hJe (by have := J.nonempty; omega)
      have hpos := count_pos_of_pick hI
      have hwt := insR_weight w' e (e + 1)
      rw [sub_self, Int.toNat_zero] at hwt
      rw [weight_add, weight_singleton]
      omega
    · push Not at htwo
      have hy : ∀ J ∈ w', J.ending ≤ e - 1 := fun J hJ => by
        have := hw' J hJ
        have := htwo J hJ
        omega
      refine p_unique hSe hy ((ih _ ?_).2 _ _ _ rfl)
      have := S.nonempty
      simp only [Interval.length, hSe] at hwN
      rw [sub_add_cancel]
      omega
  refine ⟨hP, ?_⟩
  intro y f v hN hy hv
  rcases eq_or_lt_of_le hv with hvf | hvf
  · subst hvf
    exact g_top hy
  · have hvf' : v ≤ f := by omega
    obtain ⟨C, z, hCd, hCf, hz, hyeq, -⟩ := exists_decomp hy
    have hz1 : ∀ J ∈ z, J.ending ≤ f - 1 := fun J hJ => by have := hz J hJ; omega
    subst hyeq
    rw [weight_add] at hN
    by_cases hall : ∀ c ∈ C, v ≤ c
    · refine g_none hz1 hall hvf' (hP _ ?_)
      rw [place_add, place_singleton, weight_add, weight_add, weight_seg]
      omega
    · push Not at hall
      obtain ⟨P, d, Q, rfl, hPv, hdv⟩ := exists_split C v hall
      refine g_bump hCd hCf hz1 hPv hdv hvf' ((ih _ ?_).2 _ _ _ rfl)
      have hwt := insW_weight (P ++ d :: Q) z (f - 1)
      have hle := sum_toNat_le (P ++ d :: Q) f
      rw [weight_place_coe] at hN
      simp only [sub_add_cancel] at hwt ⊢
      omega

theorem pStmt (w : Multisegment) : PStmt w := (main (weight w)).1 w rfl

end Langlands.MoeglinWaldspurger.Involution

namespace Langlands.MoeglinWaldspurger

open Involution in
/-- The Moeglin–Waldspurger recursion `dual` is an involution on all finite integer
multisegments, including the empty one and repeated intervals. -/
theorem involutivity : Involutivity := by
  intro a
  induction a using (measure fun a : Multisegment => Multiset.card a).wf.induction with
  | h a ih =>
  by_cases ha : a = 0
  · subst ha
    simp
  · have hne : a.toFinset.Nonempty := by
      obtain ⟨I, hI⟩ := Multiset.exists_mem_of_ne_zero ha
      exact ⟨I, Multiset.mem_toFinset.mpr hI⟩
    obtain ⟨T, hT, hTmax⟩ := Finset.exists_max_image a.toFinset Interval.ending hne
    have hT' : T ∈ a := Multiset.mem_toFinset.mp hT
    have hne' : (a.filter fun I => I.ending = T.ending).toFinset.Nonempty :=
      ⟨T, Multiset.mem_toFinset.mpr (Multiset.mem_filter.mpr ⟨hT', rfl⟩)⟩
    obtain ⟨S, hS, hSmin⟩ := Finset.exists_min_image _ Interval.beginning hne'
    obtain ⟨hSa, hSe⟩ := Multiset.mem_filter.mp (Multiset.mem_toFinset.mp hS)
    have hae : ∀ J ∈ a, J.ending ≤ S.ending := fun J hJ => by
      rw [hSe]
      exact hTmax J (Multiset.mem_toFinset.mpr hJ)
    have hmin : ∀ I ∈ a, I.ending = S.ending → S.beginning ≤ I.beginning := fun I hI hIe =>
      hSmin I (Multiset.mem_toFinset.mpr (Multiset.mem_filter.mpr ⟨hI, hIe.trans hSe⟩))
    rw [bridge (dual_endings a S.ending hae), pStmt a S.ending S hae hSa rfl hmin]
    dsimp only
    rw [ih (a.erase S) (Multiset.card_erase_lt_of_mem hSa), emit,
      show S.ending + 1 - (S.length : ℤ) = S.beginning by
        have := S.nonempty
        simp only [Interval.length]
        push_cast
        omega,
      seg_self, Multiset.singleton_add, Multiset.cons_erase hSa]

end Langlands.MoeglinWaldspurger
