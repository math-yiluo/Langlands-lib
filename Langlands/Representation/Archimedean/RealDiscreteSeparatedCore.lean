import Langlands.Representation.Archimedean.RealDiscreteSeparatedRelations
import Langlands.Representation.Archimedean.RealSphericalCyclic

/-!
# The scalar commutant in the separated discrete-series case, for sorted data

Let `cs` be real characters (even ones first) and `Ds` induction data of nonzero weights
(sorted by decreasing absolute weight), all with the same real exponent `r`, such that no
character has the complex exponent of a block of `Ds` and blocks of `Ds` with the same complex
exponent have the same absolute weight (`IsSepData`). Given spherical cyclicity
(`RealSphericalCyclicStatement`), the standard module of `cs, D_d, …, D_1` (`tgtList`) has a
scalar simultaneous commutant (`hasScalarCommutant_tgtList`).

The proof combines the presentation `x(D₁), …, x(D_d), cs, y(D_d), …, y(D₁) ↠ tgtList`
(`hasGKSurjection_chain`), the minor shift of the source onto the even list `midList`
(`isMinorShift_src`, `shiftList_eq_midList`), a Lie-cyclic `O(n)`-fixed vector of `midList`
obtained from spherical cyclicity of the sorted list (`exists_cyclic`), and the frame relations
(`exists_frame_rel`) in the frame criterion `hasScalarCommutant_of_frame`.
-/

noncomputable section

open Finset

open scoped TensorProduct

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean Langlands.GeneralLinear

set_option autoImplicit false

attribute [local instance 100] LieRing.ofAssociativeRing

namespace RealDiscreteSeparated

open RealDiscretePresentation RealDiscreteShift RealDiscreteSort RealDiscreteFrame
  RealTiedMinorProduct RealDiscreteMinorCyclic RealInducedCharacter RealTemperedCommutantReduction

/-! ## The hypotheses -/

/-- The data of the separated case: common real exponent `r`, even characters first, blocks
sorted by decreasing absolute weight, nonzero weights, no character at the complex exponent of a
block, and equal absolute weights for blocks with equal complex exponents. -/
structure IsSepData (r : ℝ) (cs : List RealCharacterData) (Ds : List ComplexCharacterData) :
    Prop where
  re_c : ∀ c ∈ cs, c.exponent.re = r
  re_D : ∀ e ∈ Ds, e.exponent.re = r
  sortC : cs.Pairwise fun b c => b.parity.val ≤ c.parity.val
  sortD : Ds.Pairwise fun e f => f.weight.natAbs ≤ e.weight.natAbs
  pos : ∀ e ∈ Ds, 0 < e.weight.natAbs
  sepC : ∀ c ∈ cs, ∀ e ∈ Ds, c.exponent ≠ e.exponent
  sepD : ∀ e ∈ Ds, ∀ f ∈ Ds, e.exponent = f.exponent → e.weight.natAbs = f.weight.natAbs

variable {r : ℝ} {cs : List RealCharacterData} {Ds : List ComplexCharacterData}

theorem im_ne_of_ne {a b : ℂ} (h : a ≠ b) (hre : a.re = b.re) : a.im ≠ b.im :=
  fun him => h (Complex.ext hre him)

theorem bExp_re (e : ComplexCharacterData) :
    (bExp e).re = e.exponent.re - (e.weight.natAbs : ℝ) / 2 := by
  simp [bExp]

theorem bExp_im (e : ComplexCharacterData) : (bExp e).im = e.exponent.im := by
  simp [bExp]

theorem aExp_re (e : ComplexCharacterData) :
    (aExp e).re = e.exponent.re + (e.weight.natAbs : ℝ) / 2 := by
  simp [aExp]

theorem aExp_im (e : ComplexCharacterData) : (aExp e).im = e.exponent.im := by
  simp [aExp]

theorem IsSepData.eq_of_im (h : IsSepData r cs Ds) {e f : ComplexCharacterData} (he : e ∈ Ds)
    (hf : f ∈ Ds) (him : e.exponent.im = f.exponent.im) : e.exponent = f.exponent :=
  Complex.ext (by rw [h.re_D e he, h.re_D f hf]) him

theorem IsSepData.im_ne (h : IsSepData r cs Ds) {c : RealCharacterData} {e : ComplexCharacterData}
    (hc : c ∈ cs) (he : e ∈ Ds) : c.exponent.im ≠ e.exponent.im :=
  im_ne_of_ne (h.sepC c hc e he) (by rw [h.re_c c hc, h.re_D e he])

/-! ## Unlinked pairs of the presentation -/

theorem datumExponent_of_mem_induced {e : ComplexCharacterData} {b : MoeglinDatum}
    (hb : b ∈ realBlockMoeglinData (.induced e)) :
    RealTiedScalarAssembly.datumExponent b = e.exponent := by
  simp only [realBlockMoeglinData] at hb
  split_ifs at hb
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl <;> rfl
  · simp only [List.mem_singleton] at hb
    subst hb
    rfl

theorem unlinked_x_c (h : IsSepData r cs Ds) {e : ComplexCharacterData} (he : e ∈ Ds)
    {c : RealCharacterData} (hc : c ∈ cs) :
    AreRealBlocksUnlinked (xBlock e) (.character c) := by
  refine unlinked_of_im_ne ?_
  show (bExp e).im ≠ c.exponent.im
  rw [bExp_im]
  exact (h.im_ne hc he).symm

theorem unlinked_x_D (h : IsSepData r cs Ds) {d e : ComplexCharacterData} (hd : d ∈ Ds)
    (he : e ∈ Ds) : AreRealBlocksUnlinked (xBlock d) (.induced e) := by
  by_cases ht : d.exponent = e.exponent
  · have hl := h.sepD d hd e he ht
    have hw : e.weight ≠ 0 := by
      have := h.pos e he
      omega
    intro a ha b hb hab
    rw [show realBlockMoeglinData (xBlock d) = [.character 0 (bExp d)] from rfl,
      List.mem_singleton] at ha
    simp only [realBlockMoeglinData, hw, ite_false, List.mem_singleton] at hb
    subst ha
    subst hb
    obtain ⟨k, hk, hk'⟩ := hab
    have hde : e.exponent - bExp d = (e.weight.natAbs : ℂ) / 2 := by
      rw [bExp, ht, hl]
      ring
    rcases hk' with h1 | h1
    · have h2 : (k : ℂ) = 0 := by linear_combination hde - h1
      have : k = 0 := by exact_mod_cast h2
      omega
    · have h2 : ((e.weight.natAbs + k : ℕ) : ℂ) = 0 := by
        push_cast
        linear_combination -h1 - hde
      have : e.weight.natAbs + k = 0 := by exact_mod_cast h2
      omega
  · refine unlinked_of_block_im_ne fun a ha b hb => ?_
    rw [show realBlockMoeglinData (xBlock d) = [.character 0 (bExp d)] from rfl,
      List.mem_singleton] at ha
    subst ha
    rw [datumExponent_of_mem_induced hb]
    show (bExp d).im ≠ e.exponent.im
    rw [bExp_im]
    exact fun him => ht (h.eq_of_im hd he him)

/-- **The presentation.** -/
theorem hasGKSurjection_tgtList (h : IsSepData r cs Ds) {n : ℕ}
    (hn : Ds.length + cs.length + Ds.length = n) :
    HasGKSurjection n ((srcChars cs Ds).map RealBlock.character) (tgtList cs Ds) := by
  have hrank : realRank ([] ++ sourceList Ds (cs.map RealBlock.character) ++ []) = n := by
    rw [List.nil_append, List.append_nil, sourceList_eq, realRank_map_character,
      srcChars_length, hn]
  have := hasGKSurjection_chain (n := n) (cs.map RealBlock.character) Ds [] [] hrank h.pos
    (fun d hd z hz => by
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hz
      exact unlinked_x_c h hd hc)
    (List.pairwise_of_forall_mem_list fun d hd e he => unlinked_x_D h hd he)
  rw [List.nil_append, List.append_nil, List.nil_append, List.append_nil, sourceList_eq] at this
  exact this

/-! ## The sorted spherical list -/

theorem eq_charData_of_mem_midList {c : RealCharacterData} (hc : c ∈ midList cs Ds) :
    c = RealJacquetFrobenius.charData 0 c.exponent := by
  simp only [midList, List.mem_append, List.mem_map, List.mem_reverse] at hc
  rcases hc with (⟨e, -, rfl⟩ | ⟨c', -, rfl⟩) | ⟨e, -, rfl⟩ <;> rfl

/-- The midList has no linked out-of-order pair: an earlier entry with smaller real exponent
has a different imaginary part. -/
theorem pairwise_midList (h : IsSepData r cs Ds) :
    (midList cs Ds).Pairwise fun c b => c.exponent.re < b.exponent.re →
      c.exponent.im ≠ b.exponent.im := by
  have hpos := h.pos
  unfold midList
  rw [List.pairwise_append, List.pairwise_append]
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · -- the `x`-rows
    rw [List.pairwise_map]
    refine List.pairwise_of_forall_mem_list fun e he f hf hlt him => ?_
    change (bExp e).re < (bExp f).re at hlt
    change (bExp e).im = (bExp f).im at him
    rw [bExp_im, bExp_im] at him
    have ht := h.eq_of_im he hf him
    have hl := h.sepD e he f hf ht
    rw [bExp_re, bExp_re, ht, hl] at hlt
    exact lt_irrefl _ hlt
  · -- the characters
    rw [List.pairwise_map]
    refine h.sortC.imp_of_mem fun {b c} hb hc hbc hlt _ => ?_
    change (b.exponent - (b.parity.val : ℂ)).re < (c.exponent - (c.parity.val : ℂ)).re at hlt
    simp only [Complex.sub_re, Complex.natCast_re, h.re_c b hb, h.re_c c hc] at hlt
    have : (b.parity.val : ℝ) ≤ c.parity.val := by exact_mod_cast hbc
    linarith
  · -- `x`-rows against characters
    intro a ha b hb _ him
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
    change (bExp e).im = (c.exponent - (c.parity.val : ℂ)).im at him
    rw [bExp_im, Complex.sub_im, Complex.natCast_im, sub_zero] at him
    exact h.im_ne hc he him.symm
  · -- the `y`-rows
    rw [List.pairwise_map]
    refine List.pairwise_of_forall_mem_list fun e he f hf hlt him => ?_
    rw [List.mem_reverse] at he hf
    change (aExp e - ((e.weight.natAbs + 1 : ℕ) : ℂ)).re <
      (aExp f - ((f.weight.natAbs + 1 : ℕ) : ℂ)).re at hlt
    change (aExp e - ((e.weight.natAbs + 1 : ℕ) : ℂ)).im =
      (aExp f - ((f.weight.natAbs + 1 : ℕ) : ℂ)).im at him
    rw [Complex.sub_im, Complex.sub_im, Complex.natCast_im, Complex.natCast_im, sub_zero,
      sub_zero, aExp_im, aExp_im] at him
    have ht := h.eq_of_im he hf him
    have hl := h.sepD e he f hf ht
    rw [Complex.sub_re, Complex.sub_re, aExp_re, aExp_re, ht, hl] at hlt
    exact lt_irrefl _ hlt
  · -- `x`-rows and characters against `y`-rows
    intro a ha b hb hlt him
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hb
    rw [List.mem_reverse] at hf
    have hf1 := hpos f hf
    have hf1' : (1 : ℝ) ≤ f.weight.natAbs := by exact_mod_cast hf1
    change _ < (aExp f - ((f.weight.natAbs + 1 : ℕ) : ℂ)).re at hlt
    change _ = (aExp f - ((f.weight.natAbs + 1 : ℕ) : ℂ)).im at him
    rw [Complex.sub_im, Complex.natCast_im, sub_zero, aExp_im] at him
    rw [Complex.sub_re, Complex.natCast_re, aExp_re, h.re_D f hf] at hlt
    push_cast at hlt
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
      change (bExp e).re < _ at hlt
      change (bExp e).im = _ at him
      rw [bExp_im] at him
      have ht := h.eq_of_im he hf him
      have hl := h.sepD e he f hf ht
      rw [bExp_re, h.re_D e he, hl] at hlt
      linarith
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
      change (c.exponent - (c.parity.val : ℂ)).re < _ at hlt
      rw [Complex.sub_re, Complex.natCast_re, h.re_c c hc] at hlt
      have hp : (c.parity.val : ℝ) ≤ 1 := by
        have := c.parity.isLt
        exact_mod_cast (by omega : c.parity.val ≤ 1)
      linarith

theorem sphList_sorted (n : ℕ) {L : List RealCharacterData} (hL : L.length = n)
    (hc : ∀ c ∈ L, c = RealJacquetFrobenius.charData 0 c.exponent) :
    sphList n (L.map RealBlock.character) ∅ = L := by
  apply List.ext_getElem
  · rw [sphList_length, hL]
  · intro i h₁ h₂
    simp only [sphList, List.getElem_ofFn, shiftExp, Finset.notMem_empty, ite_false, sub_zero]
    rw [realPositionExponent_map_character L i h₂]
    exact (hc _ (List.getElem_mem h₂)).symm

/-- **A Lie-cyclic fixed vector of the even list.** -/
theorem exists_cyclic (hS : RealSphericalCyclicStatement) (h : IsSepData r cs Ds) {n : ℕ}
    (hn : Ds.length + cs.length + Ds.length = n) :
    ∃ T : RealDiscretePresentation.KF n ((midList cs Ds).map RealBlock.character),
      (∀ k, realStandardRep n ((midList cs Ds).map RealBlock.character) k T = T) ∧
      ∀ W : Submodule ℂ (RealDiscretePresentation.KF n ((midList cs Ds).map RealBlock.character)),
        T ∈ W → (∀ Z : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ, ∀ w ∈ W,
          realStandardLie n ((midList cs Ds).map RealBlock.character) Z w ∈ W) → W = ⊤ := by
  set L := midList cs Ds with hLdef
  set srt := L.insertionSort LangRel with hsrt
  have hLn : L.length = n := by rw [hLdef, midList_length, hn]
  have hsn : srt.length = n := by rw [hsrt, List.length_insertionSort, hLn]
  have hsph : sphList n (srt.map RealBlock.character) ∅ = srt :=
    sphList_sorted n hsn fun c hc =>
      eq_charData_of_mem_midList ((List.perm_insertionSort LangRel L).subset hc)
  have hrank : realRank ([] ++ L.map RealBlock.character ++ []) = n := by
    rw [List.nil_append, List.append_nil, realRank_map_character, hLn]
  have hsort := hasGKSurjection_insertionSort (n := n) L [] [] hrank
    ((pairwise_midList h).imp fun hcb hlt => unlinked_of_im_ne (hcb hlt))
  rw [List.nil_append, List.append_nil, List.nil_append, List.append_nil] at hsort
  have hsurj : HasGKSurjection n (sphBlocks n (srt.map RealBlock.character) ∅)
      (L.map RealBlock.character) :=
    (HasGKSurjection.of_eq (by rw [sphBlocks, hsph])).trans hsort
  obtain ⟨q, hqs, hq⟩ := hsurj
  have hord : IsRealLanglandsOrdered
      ((sphList n (srt.map RealBlock.character) ∅).map RealBlock.character) := by
    rw [hsph]
    exact isRealLanglandsOrdered_insertionSort L
  exact ⟨_, cyclic_map hqs hq (sphVec_fixed ∅) fun W hW hWL =>
    hS n _ (sphList_length _) (sphList_parity _) hord (sphVec ∅) (sphVec_fixed ∅)
      (sphVec_ne_zero ∅) W hW hWL⟩

/-! ## The scalar commutant -/

/-- A bound `N` for the numbers `|m| + 1`. -/
def bound : List ComplexCharacterData → ℕ
  | [] => 1
  | e :: Es => max (e.weight.natAbs + 1) (bound Es)

theorem one_le_bound : ∀ Es : List ComplexCharacterData, 1 ≤ bound Es
  | [] => le_rfl
  | _ :: Es => le_trans (one_le_bound Es) (le_max_right _ _)

theorem le_bound : ∀ (Es : List ComplexCharacterData), ∀ e ∈ Es, e.weight.natAbs + 1 ≤ bound Es
  | [], _, he => absurd he List.not_mem_nil
  | f :: Es, e, he => by
      rcases List.mem_cons.mp he with rfl | he
      · exact le_max_left _ _
      · exact le_trans (le_bound Es e he) (le_max_right _ _)

/-- **The separated case for sorted data**, given spherical cyclicity. -/
theorem hasScalarCommutant_tgtList (hS : RealSphericalCyclicStatement) (h : IsSepData r cs Ds)
    {n : ℕ} (hn : Ds.length + cs.length + Ds.length = n) :
    HasScalarCommutant n (tgtList cs Ds) := by
  have hN := le_bound Ds
  have hN1 := one_le_bound Ds
  obtain ⟨Φ, hΦs, hΦ⟩ := hasGKSurjection_tgtList h hn
  have hsh := isMinorShift_src (N := bound Ds) hn h.sortD h.sortC hN hN1
  rw [shiftList_eq_midList hn hN hN1] at hsh
  obtain ⟨T, hT, hcyc⟩ := exists_cyclic hS h hn
  have hev : (n - cs.length) % 2 = 0 := by omega
  exact hasScalarCommutant_of_frame hsh hT hcyc (frameU_mul_frameV hev) hΦs hΦ
    (fun D => (exists_frame_rel hn hN hN1 hsh hT D).choose) (tgtSet cs Ds n (bound Ds) ∅)
    (fun L hL D => (exists_frame_rel hn hN hN1 hsh hT D).choose_spec L hL)

end RealDiscreteSeparated

end Langlands.Archimedean
