import Langlands.Representation.Classification.MoeglinWaldspurgerInsertion

/-!
# Word insertion through several rows and the Knuth-type system lemma

Inserting a word at row `g` of a multisegment runs the abstract row insertion of
`MoeglinWaldspurgerRowInsertion` on row `g` and passes the bumped entries to row
`g - 1` (`rdw`).  Consequences: weakly decreasing words have weakly decreasing bump
counts (`m1`), the emitted intervals of `dual` are monotone (`mono`), and the words
`P ++ d :: Q ++ [e]` and `d :: (P ++ e :: Q)` give the same multisegment with bump
counts related by the count fact `CF` (`system`).
-/

namespace Langlands.MoeglinWaldspurger.Involution

open Row (Desc rRun rIns KP SRLOut)

/-- Bump counts at the current row from the bump outputs at this row and the counts
of the bumped letters one row lower. -/
def combine : List (Option ℤ) → List ℕ → List ℕ
  | [], _ => []
  | none :: os, cs => 0 :: combine os cs
  | some _ :: os, [] => 1 :: combine os []
  | some _ :: os, c :: cs => (c + 1) :: combine os cs

@[simp] theorem combine_nil (cs : List ℕ) : combine [] cs = [] := rfl

@[simp] theorem combine_none (os : List (Option ℤ)) (cs : List ℕ) :
    combine (none :: os) cs = 0 :: combine os cs := rfl

@[simp] theorem combine_some (a : ℤ) (os : List (Option ℤ)) (c : ℕ) (cs : List ℕ) :
    combine (some a :: os) (c :: cs) = (c + 1) :: combine os cs := rfl

theorem combine_map_some (A : List ℤ) (os : List (Option ℤ)) : ∀ (cs₁ cs₂ : List ℕ),
    cs₁.length = A.length →
    combine (A.map some ++ os) (cs₁ ++ cs₂) = cs₁.map (· + 1) ++ combine os cs₂ := by
  induction A with
  | nil =>
    intro cs₁ cs₂ h
    cases cs₁ with
    | nil => simp
    | cons c cs₁ => simp at h
  | cons a A ih =>
    intro cs₁ cs₂ h
    cases cs₁ with
    | nil => simp at h
    | cons c cs₁ =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp only [List.map_cons, List.cons_append, combine_some]
      rw [ih cs₁ cs₂ h]

theorem combine_replicate (k : ℕ) (os : List (Option ℤ)) (cs : List ℕ) :
    combine (List.replicate k none ++ os) cs = List.replicate k 0 ++ combine os cs := by
  induction k with
  | zero => simp
  | succ k ih => simp [List.replicate_succ, ih]

theorem combine_replicate_nil (k : ℕ) (cs : List ℕ) :
    combine (List.replicate k none) cs = List.replicate k 0 := by
  have := combine_replicate k [] cs
  simpa using this

@[simp] theorem filterMap_id_map_some (A : List ℤ) : (A.map some).filterMap id = A := by
  induction A with
  | nil => rfl
  | cons a A ih => simp

@[simp] theorem filterMap_id_replicate_none (k : ℕ) :
    (List.replicate k (none : Option ℤ)).filterMap id = [] := by
  induction k with
  | zero => rfl
  | succ k ih => simp

/-! ## Word insertion at a row -/

/-- Inserting a word at row `g`: the abstract row insertion runs on row `g`, and its
bumped entries are inserted, in order, at row `g - 1`. -/
theorem rdw (w : List ℤ) : ∀ (R : List ℤ) (z : Multisegment) (g : ℤ), Desc R →
    (∀ x ∈ R, x ≤ g + 1) → (∀ a ∈ w, a ≤ g + 1) → (∀ J ∈ z, J.ending < g) →
    insW (place ↑R g + z) g w =
      ((insW z (g - 1) ((rRun R w).2.filterMap id)).1 + place ↑(rRun R w).1 g,
        combine (rRun R w).2 (insW z (g - 1) ((rRun R w).2.filterMap id)).2) := by
  induction w with
  | nil => intro R z g _ _ _ _; simp [add_comm]
  | cons a w ih =>
    intro R z g hR hRg hw hz
    have ha : a ≤ g + 1 := hw a List.mem_cons_self
    have hw' : ∀ b ∈ w, b ≤ g + 1 := fun b hb => hw b (List.mem_cons_of_mem _ hb)
    have hR1 : Desc (rIns R a).1 := Row.rIns_desc a hR
    have hR1g : ∀ x ∈ (rIns R a).1, x ≤ g + 1 := fun x hx => by
      rcases Row.mem_rIns hx with h | h
      · exact hRg x h
      · rw [h]; exact ha
    rw [insW_cons, Row.rRun_cons]
    cases ho : (rIns R a).2 with
    | none =>
      have hall := (Row.rIns_none_iff R a).mp ho
      have hcoe : ((rIns R a).1 : Multiset ℤ) = ↑R + {a} := by
        rw [Row.rIns_of_none hall]
        show ((R ++ [a] : List ℤ) : Multiset ℤ) = _
        rw [← Multiset.coe_add, Multiset.coe_singleton]
      rw [rd1_none (fun x hx => hall x (Multiset.mem_coe.mp hx)) hz, ← hcoe,
        ih _ z g hR1 hR1g hw' hz]
      simp
    | some m =>
      obtain ⟨hm, hma, hmax, hR1eq⟩ := Row.rIns_some hR ho
      have hz1 : ∀ J ∈ (insR z (g - 1) m).1, J.ending < g := fun J hJ => by
        have := insR_endings z (g - 1) m (g - 1) (fun K hK => by have := hz K hK; omega)
          le_rfl J hJ
        omega
      rw [rd1_some (Multiset.mem_coe.mpr hm) hma (fun x hx => hmax x (Multiset.mem_coe.mp hx))
        ha hz, ← hR1eq, add_comm (insR z (g - 1) m).1, ih _ _ g hR1 hR1g hw' hz1]
      simp [insW_cons]

theorem card_place_pos {R : List ℤ} {g : ℤ} (hRg : ∀ x ∈ R, x ≤ g) (hne : R ≠ []) :
    0 < (place ↑R g).card := by
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil R hne
  exact Multiset.card_pos_iff_exists_mem.mpr
    ⟨⟨x, g, hRg x hx⟩, mem_place.mpr ⟨Multiset.mem_coe.mpr hx, rfl⟩⟩

theorem exists_decomp {z : Multisegment} {g : ℤ} (hz : ∀ J ∈ z, J.ending ≤ g) :
    ∃ (R : List ℤ) (z' : Multisegment), Desc R ∧ (∀ x ∈ R, x ≤ g) ∧
      (∀ J ∈ z', J.ending < g) ∧ z = place ↑R g + z' ∧ (R ≠ [] → z'.card < z.card) := by
  refine ⟨rowL z g, low z g, rowL_desc z g, fun x hx => rowL_le hx, low_endings z g,
    decomp z g hz, fun hne => ?_⟩
  have h := congrArg Multiset.card (decomp z g hz)
  rw [Multiset.card_add] at h
  have := card_place_pos (fun x hx => rowL_le hx) hne
  omega

/-! ## Monotone counts -/

/-- A weakly decreasing word has weakly decreasing bump counts. -/
theorem m1 (z : Multisegment) : ∀ (g : ℤ) (w : List ℤ), (∀ J ∈ z, J.ending ≤ g) → Desc w →
    (∀ a ∈ w, a ≤ g + 1) → (insW z g w).2.Pairwise (fun x y => y ≤ x) := by
  induction z using (measure (fun a : Multisegment => a.card)).wf.induction with
  | h z ih =>
    intro g w hz hw hwg
    obtain ⟨R, z', hR, hRg, hz', hzeq, hcard⟩ := exists_decomp hz
    obtain ⟨A, k, hout, hsub⟩ := Row.rRun_decOuts R w hR hw
    rw [hzeq, rdw w R z' g hR (fun x hx => by have := hRg x hx; omega) hwg hz', hout]
    have hfm : (A.map some ++ List.replicate k none).filterMap id = A := by
      simp [List.filterMap_append]
    rw [hfm]
    by_cases hA : A = []
    · subst hA
      simp [combine_replicate_nil, List.pairwise_replicate]
    · have hRne : R ≠ [] := by
        rintro rfl
        exact hA (List.eq_nil_of_sublist_nil hsub)
      have hcs := ih z' (hcard hRne) (g - 1) A (fun J hJ => by have := hz' J hJ; omega)
        (hR.sublist hsub) (fun a ha => by have := hRg a (hsub.subset ha); omega)
      have hlen := insW_length A z' (g - 1)
      have := combine_map_some A (List.replicate k none) (insW z' (g - 1) A).2 [] hlen
      rw [List.append_nil] at this
      rw [this, combine_replicate_nil]
      refine List.pairwise_append.mpr ⟨?_, ?_, ?_⟩
      · exact List.pairwise_map.mpr (hcs.imp (fun h => by omega))
      · simp [List.pairwise_replicate]
      · intro x _ y hy
        rw [List.eq_of_mem_replicate hy]
        exact Nat.zero_le _

/-- In `dual` of the residual of a round, every interval at the top row is no longer
than the interval emitted by the round. -/
theorem mono (y : Multisegment) (f : ℤ) (hy : ∀ J ∈ y, J.ending ≤ f) :
    ∀ J ∈ dual (insR y f (f + 1)).1, J.ending = f →
      f + 1 - ((insR y f (f + 1)).2 : ℤ) ≤ J.beginning := by
  obtain ⟨C, z, hC, hCf, hz, hyeq, -⟩ := exists_decomp hy
  rw [hyeq]
  cases C with
  | nil =>
    have h := rd1_none (M := 0) (z' := z) (g := f) (v := f + 1) (by simp) hz
    simp only [Multiset.coe_nil] at h ⊢
    rw [h, zero_add, place_singleton, seg_of_lt (by omega), zero_add]
    intro J hJ hJe
    have := dual_endings z (f - 1) (fun K hK => by have := hz K hK; omega) J hJ
    omega
  | cons c C' =>
    have hcf : c ≤ f := hCf c List.mem_cons_self
    have hcmax : ∀ x ∈ (↑(c :: C') : Multiset ℤ), x < f + 1 → x ≤ c := by
      intro x hx _
      rcases List.mem_cons.mp (Multiset.mem_coe.mp hx) with rfl | hx
      · exact le_rfl
      · exact (List.pairwise_cons.mp hC).1 x hx
    have hz1 := insR_endings z (f - 1) c (f - 1) (fun K hK => by have := hz K hK; omega) le_rfl
    rw [rd1_some (Multiset.mem_coe.mpr List.mem_cons_self) (by omega) hcmax le_rfl hz]
    dsimp only
    rw [← Multiset.cons_coe, Multiset.erase_cons_head, place_add, place_singleton,
      seg_of_lt (by omega : f < f + 1), add_zero, add_comm (insR z (f - 1) c).1,
      rowProc C' f _ (List.pairwise_cons.mp hC).2 (fun x hx => hCf x (List.mem_cons_of_mem _ hx))
        hz1]
    have hm := m1 z (f - 1) (c :: C') (fun K hK => by have := hz K hK; omega) hC
      (fun x hx => by have := hCf x hx; omega)
    rw [insW_cons] at hm
    intro J hJ hJe
    rcases Multiset.mem_add.mp hJ with hJ | hJ
    · obtain ⟨hJb, -⟩ := mem_place.mp hJ
      obtain ⟨r', hr', hJr⟩ := List.mem_map.mp (Multiset.mem_coe.mp hJb)
      have := (List.pairwise_cons.mp hm).1 r' hr'
      push_cast
      omega
    · have := dual_endings _ (f - 1) (insW_endings C' _ (f - 1) (f - 1) hz1 le_rfl) J hJ
      omega

/-! ## The system lemma -/

/-- The count fact relating the bump counts `r ++ [t]` of `P ++ d :: Q ++ [e]` and
`r' :: s` of `d :: (P ++ e :: Q)`. -/
def CF (r : List ℕ) (t r' : ℕ) (s : List ℕ) : Prop :=
  (↑s : Multiset ℕ) + {r'} = ↑r + {t} ∧ r' < t ∧ ∀ x ∈ s, r' < x → t ≤ x

/-- The Knuth-type system lemma for word insertion into a multisegment. -/
theorem system (z : Multisegment) : ∀ (g : ℤ) (P Q : List ℤ) (d e : ℤ),
    (∀ J ∈ z, J.ending ≤ g) → KP P d Q e → (∀ x ∈ P ++ d :: Q ++ [e], x ≤ g + 1) →
    (insW z g (P ++ d :: Q ++ [e])).1 = (insW z g (d :: (P ++ e :: Q))).1 ∧
    ∃ (r : List ℕ) (t r' : ℕ) (s : List ℕ), (insW z g (P ++ d :: Q ++ [e])).2 = r ++ [t] ∧
      (insW z g (d :: (P ++ e :: Q))).2 = r' :: s ∧ CF r t r' s := by
  induction z using (measure (fun a : Multisegment => a.card)).wf.induction with
  | h z ih =>
    intro g P Q d e hz hKP hlet
    have hletX : ∀ x ∈ d :: (P ++ e :: Q), x ≤ g + 1 := by
      intro x hx
      apply hlet
      simp only [List.mem_cons, List.mem_append] at hx ⊢
      tauto
    obtain ⟨R, z', hR, hRg, hz', hzeq, hcard⟩ := exists_decomp hz
    have hRg1 : ∀ x ∈ R, x ≤ g + 1 := fun x hx => by have := hRg x hx; omega
    rw [hzeq, rdw _ R z' g hR hRg1 hlet hz', rdw _ R z' g hR hRg1 hletX hz']
    obtain ⟨hrow, A, ε, k, hY, hA, hε, hX⟩ := Row.srl R P Q d e hR hKP
    rw [hrow, hY]
    have hd : d ≤ g := by
      have := hKP.2.2
      have := hlet e (by simp)
      omega
    have hεg : ε ≤ g := by
      rcases hε with h | h
      · exact hRg ε h
      · omega
    have hAg : ∀ x ∈ A, x ≤ g := fun x hx => hRg x (hA x hx)
    have hz'g : ∀ J ∈ z', J.ending ≤ g - 1 := fun J hJ => by have := hz' J hJ; omega
    rcases hX with ⟨hk, hdesc, hXo⟩ | ⟨hRne, A₁, a, A₂, hAeq, hKP', hXo⟩
    · -- both words bump the same word `A ++ [ε]`
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      rw [hXo]
      have hfY : (A.map some ++ List.replicate (k' + 1) none ++ [some ε]).filterMap id =
          A ++ [ε] := by
        simp [List.filterMap_append]
      have hfX : (none :: ((A ++ [ε]).map some ++ List.replicate (k' + 1 - 1) none)).filterMap id =
          A ++ [ε] := by
        simp [List.filterMap_append]
      rw [hfY, hfX]
      refine ⟨rfl, ?_⟩
      have hcs : (insW z' (g - 1) (A ++ [ε])).2 = (insW z' (g - 1) A).2 ++
          [(insR (insW z' (g - 1) A).1 (g - 1) ε).2] := by
        rw [insW_append]
        simp [insW_cons]
      have hmono := m1 z' (g - 1) (A ++ [ε]) hz'g hdesc (fun x hx => by
        rcases List.mem_append.mp hx with hx | hx
        · have := hAg x hx; omega
        · rw [List.mem_singleton.mp hx]; omega)
      have hlen := insW_length A z' (g - 1)
      rw [hcs] at hmono
      rw [hcs]
      generalize (insW z' (g - 1) A).2 = cs₀ at hmono hlen ⊢
      generalize (insR (insW z' (g - 1) A).1 (g - 1) ε).2 = cε at hmono ⊢
      have hcY : combine (A.map some ++ List.replicate (k' + 1) none ++ [some ε]) (cs₀ ++ [cε]) =
          (cs₀.map (· + 1) ++ List.replicate (k' + 1) 0) ++ [cε + 1] := by
        rw [List.append_assoc (A.map some), combine_map_some A _ cs₀ [cε] hlen, combine_replicate]
        simp
      have hcX : combine (none :: ((A ++ [ε]).map some ++ List.replicate (k' + 1 - 1) none))
          (cs₀ ++ [cε]) = 0 :: ((cs₀ ++ [cε]).map (· + 1) ++ List.replicate k' 0) := by
        have h := combine_map_some (A ++ [ε]) (List.replicate k' none) (cs₀ ++ [cε]) []
          (by simp [hlen])
        rw [List.append_nil] at h
        rw [Nat.add_sub_cancel, combine_none, h, combine_replicate_nil]
      refine ⟨_, _, _, _, hcY, hcX, ?_, by omega, ?_⟩
      · rw [← Multiset.coe_singleton, ← Multiset.coe_singleton, Multiset.coe_add, Multiset.coe_add,
          Multiset.coe_eq_coe, List.perm_iff_count]
        intro x
        simp only [List.count_append, List.map_append, List.count_replicate, List.map_cons,
          List.map_nil, List.count_singleton]
        split_ifs <;> omega
      · intro x hx hx0
        rcases List.mem_append.mp hx with hx | hx
        · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
          rcases List.mem_append.mp hc with hc | hc
          · have := (List.pairwise_append.mp hmono).2.2 c hc cε (List.mem_singleton_self _)
            omega
          · rw [List.mem_singleton.mp hc]
        · rw [List.eq_of_mem_replicate hx] at hx0
          omega
    · -- the bumped words form a Knuth pair one row lower
      subst hAeq
      rw [hXo]
      have hfY : ((A₁ ++ a :: A₂).map some ++ List.replicate k none ++ [some ε]).filterMap id =
          A₁ ++ a :: A₂ ++ [ε] := by
        simp [List.filterMap_append]
      have hfX : (some a :: ((A₁ ++ ε :: A₂).map some ++ List.replicate k none)).filterMap id =
          a :: (A₁ ++ ε :: A₂) := by
        simp [List.filterMap_append]
      have hlet' : ∀ x ∈ A₁ ++ a :: A₂ ++ [ε], x ≤ g - 1 + 1 := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · have := hAg x hx; omega
        · rw [List.mem_singleton.mp hx]; omega
      obtain ⟨hfin, ρ, τ, ρ', σ, hρ, hσ, hcf⟩ :=
        ih z' (hcard hRne) (g - 1) A₁ A₂ a ε hz'g hKP' hlet'
      rw [hfY, hfX, hfin]
      refine ⟨rfl, ?_⟩
      have hρlen : ρ.length = (A₁ ++ a :: A₂).length := by
        have := insW_length (A₁ ++ a :: A₂ ++ [ε]) z' (g - 1)
        rw [hρ] at this
        simp at this
        simp
        omega
      have hσlen : σ.length = (A₁ ++ ε :: A₂).length := by
        have := insW_length (a :: (A₁ ++ ε :: A₂)) z' (g - 1)
        rw [hσ] at this
        simpa using this
      rw [hρ, hσ]
      have hcY : combine ((A₁ ++ a :: A₂).map some ++ List.replicate k none ++ [some ε])
          (ρ ++ [τ]) = (ρ.map (· + 1) ++ List.replicate k 0) ++ [τ + 1] := by
        rw [List.append_assoc ((A₁ ++ a :: A₂).map some), combine_map_some _ _ ρ [τ] hρlen,
          combine_replicate]
        simp
      have hcX : combine (some a :: ((A₁ ++ ε :: A₂).map some ++ List.replicate k none))
          (ρ' :: σ) = (ρ' + 1) :: (σ.map (· + 1) ++ List.replicate k 0) := by
        have h := combine_map_some (A₁ ++ ε :: A₂) (List.replicate k none) σ [] hσlen
        rw [List.append_nil] at h
        rw [combine_some, h, combine_replicate_nil]
      refine ⟨_, _, _, _, hcY, hcX, ?_, by have := hcf.2.1; omega, ?_⟩
      · have h1 := congrArg (Multiset.map (· + 1)) hcf.1
        simp only [Multiset.map_add, Multiset.map_singleton, Multiset.map_coe] at h1
        rw [← Multiset.coe_add, ← Multiset.coe_add, add_right_comm, h1, add_right_comm]
      · intro x hx hx0
        rcases List.mem_append.mp hx with hx | hx
        · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
          have := hcf.2.2 y hy (by omega)
          omega
        · rw [List.eq_of_mem_replicate hx] at hx0
          omega

end Langlands.MoeglinWaldspurger.Involution
