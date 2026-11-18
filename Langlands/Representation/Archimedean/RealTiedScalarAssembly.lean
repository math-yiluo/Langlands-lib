import Langlands.Representation.Archimedean.RealTiedMinorProduct
import Langlands.Representation.Archimedean.RealLinkedLanglandsQuotientNotLargeProof
import Langlands.Representation.Archimedean.RealLinkedJacquetPairReduction
import Langlands.Representation.Archimedean.RealLanglandsQuotientReduction
import Langlands.Representation.Archimedean.RealSphericalCyclic
import Langlands.Representation.Archimedean.RealTiedScalarCommutantCases

/-!
# The scalar commutant for tied real standard modules without discrete series

Assembly of the scalar step (`RealTiedMinorScalar`) and the product reduction
(`RealTiedMinorProduct`) for tied lists of real blocks without discrete-series block, given
the cyclicity of the `O(n)`-fixed vector in a spherical principal series in the closed
Langlands chamber (carried as the hypothesis `RealSphericalCyclicStatement`). The result is
`realTiedNondiscreteReduction : RealTiedNondiscreteReductionStatement`, that is,
`RealSphericalCyclicStatement → RealTiedNondiscreteScalarCommutantStatement`.
-/

noncomputable section

open Finset

open scoped TensorProduct

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

attribute [local instance 100] LieRing.ofAssociativeRing

namespace RealTiedScalarAssembly

open RealTemperedCommutantReduction RealTiedMinorScalar RealTiedMinorProduct GramFormula

/-! ## Transfer along injective intertwiners in both directions -/

section Transfer

variable {K : Type*} [Group K] {L : Type*} [LieRing L] [LieAlgebra ℂ L]
  {V₁ V₂ : Type*} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]

/-- If `T : V₁ → V₂` and `S : V₂ → V₁` are injective intertwiners and every endomorphism of
`V₁` is scalar, then every endomorphism of `V₂` is scalar. -/
theorem endomorphismsAreScalar_of_injective
    {ρ₁ : Representation ℂ K V₁} {π₁ : L →ₗ⁅ℂ⁆ Module.End ℂ V₁}
    {ρ₂ : Representation ℂ K V₂} {π₂ : L →ₗ⁅ℂ⁆ Module.End ℂ V₂}
    (T : V₁ →ₗ[ℂ] V₂) (S : V₂ →ₗ[ℂ] V₁) (hT : Function.Injective T)
    (hS : Function.Injective S)
    (hTρ : ∀ k v, T (ρ₁ k v) = ρ₂ k (T v)) (hTπ : ∀ X v, T (π₁ X v) = π₂ X (T v))
    (hSρ : ∀ k v, S (ρ₂ k v) = ρ₁ k (S v)) (hSπ : ∀ X v, S (π₂ X v) = π₁ X (S v))
    (h : GKModuleOrthogonal.EndomorphismsAreScalar ρ₁ π₁) :
    GKModuleOrthogonal.EndomorphismsAreScalar ρ₂ π₂ := by
  intro E hEρ hEπ
  obtain ⟨d, hd⟩ := h (S ∘ₗ T) (fun k v => by simp only [LinearMap.comp_apply, hTρ, hSρ])
    (fun X v => by simp only [LinearMap.comp_apply, hTπ, hSπ])
  obtain ⟨c, hc⟩ := h (S ∘ₗ E ∘ₗ T)
    (fun k v => by simp only [LinearMap.comp_apply, hTρ, hEρ, hSρ])
    (fun X v => by simp only [LinearMap.comp_apply, hTπ, hEπ, hSπ])
  simp only [LinearMap.comp_apply] at hd hc
  by_cases hd0 : d = 0
  · have h1 : ∀ v : V₁, v = 0 := fun v =>
      hT (hS (by rw [hd, hd0, zero_smul, map_zero, map_zero]))
    refine ⟨0, fun w => ?_⟩
    have hw : w = 0 := hS (by rw [h1 (S w), map_zero])
    rw [hw, map_zero, smul_zero]
  · have hTS : ∀ w, T (S w) = d • w := fun w => hS (by rw [hd, map_smul])
    refine ⟨c / d, fun w => ?_⟩
    have h2 : (d * d) • E w = (c * d) • w := by
      have h3 := congrArg T (hc (S w))
      simp only [hTS, map_smul, smul_smul] at h3
      exact h3
    calc E w = (d * d)⁻¹ • ((d * d) • E w) := by
          rw [smul_smul, inv_mul_cancel₀ (mul_ne_zero hd0 hd0), one_smul]
      _ = (c / d) • w := by
          rw [h2, smul_smul]
          congr 1
          field_simp

end Transfer

/-- The scalar commutant transfers along injective intertwiners in both directions. -/
theorem hasScalarCommutant_of_twoWay {n : ℕ} {ds es : List RealBlock}
    (h₁ : RealInjectiveIntertwinerExists n ds es) (h₂ : RealInjectiveIntertwinerExists n es ds)
    (h : HasScalarCommutant n ds) : HasScalarCommutant n es := by
  obtain ⟨T, hTi, hT⟩ := h₁
  obtain ⟨S, hSi, hS⟩ := h₂
  exact endomorphismsAreScalar_of_injective T S hTi hSi hT.map_realStandardRep
    hT.map_realStandardLie hS.map_realStandardRep hS.map_realStandardLie h

/-! ## Tied blocks are unlinked -/

/-- The exponent `s` of a Mœglin datum `(n_j, s, σ_j)`. -/
def datumExponent : MoeglinDatum → ℂ
  | .character _ s => s
  | .discrete _ s => s

/-- Mœglin data whose exponents have equal real parts are not linked. -/
theorem not_isLinked_of_re_eq {a b : MoeglinDatum}
    (h : (datumExponent a).re = (datumExponent b).re) : ¬ a.IsLinked b := by
  rcases a with ⟨ε, s⟩ | ⟨p, s⟩ <;> rcases b with ⟨ε', s'⟩ | ⟨p', s'⟩ <;>
    simp only [datumExponent] at h <;> simp only [MoeglinDatum.IsLinked]
  · rintro ⟨k, hk, hs, -⟩
    have h1 := congrArg Complex.re hs
    simp only [Complex.sub_re, Complex.intCast_re] at h1
    exact hk (by exact_mod_cast (by linarith : (k : ℝ) = 0))
  · rintro ⟨k, hk, hs | hs⟩ <;> have h1 := congrArg Complex.re hs <;>
      have hk' : (0 : ℝ) < k := Nat.cast_pos.mpr hk <;>
      have hp : (0 : ℝ) ≤ p' := Nat.cast_nonneg p' <;>
      simp only [Complex.sub_re, Complex.add_re, Complex.div_ofNat_re, Complex.natCast_re] at h1 <;>
      linarith
  · rintro ⟨k, hk, hs | hs⟩ <;> have h1 := congrArg Complex.re hs <;>
      have hk' : (0 : ℝ) < k := Nat.cast_pos.mpr hk <;>
      have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p <;>
      simp only [Complex.sub_re, Complex.add_re, Complex.div_ofNat_re, Complex.natCast_re] at h1 <;>
      linarith
  · rintro ⟨k, hk, hs | hs⟩ <;> have h1 := congrArg Complex.re hs <;>
      have hk' : (0 : ℝ) < k := Nat.cast_pos.mpr hk <;>
      have hp : (0 : ℝ) ≤ (((p : ℤ) - p').natAbs : ℕ) := Nat.cast_nonneg _ <;>
      simp only [Complex.sub_re, Complex.add_re, Complex.div_ofNat_re, Complex.natCast_re] at h1 <;>
      linarith

/-- Every Mœglin datum of a real block has the real exponent of the block. -/
theorem datumExponent_re_of_mem {x : RealBlock} {a : MoeglinDatum}
    (ha : a ∈ realBlockMoeglinData x) : (datumExponent a).re = realBlockExponent x := by
  rcases x with c | d
  · simp only [realBlockMoeglinData, List.mem_singleton] at ha
    subst ha
    rfl
  · simp only [realBlockMoeglinData] at ha
    split_ifs at ha
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl <;> rfl
    · simp only [List.mem_singleton] at ha
      subst ha
      rfl

/-- Two real blocks with equal real exponents are unlinked. -/
theorem areRealBlocksUnlinked_of_eq {x y : RealBlock}
    (h : realBlockExponent x = realBlockExponent y) : AreRealBlocksUnlinked x y :=
  fun _ ha _ hb => not_isLinked_of_re_eq (by
    rw [datumExponent_re_of_mem ha, datumExponent_re_of_mem hb, h])

/-! ## Permutations of tied lists -/

/-- A permutation of the tied part `l₁` of a list gives an injective intertwiner. -/
theorem realInjectiveIntertwinerExists_perm {n : ℕ} {r : ℝ} {l₁ l₂ : List RealBlock}
    (h : l₁.Perm l₂) :
    ∀ pre : List RealBlock, realRank (pre ++ l₁) = n → (∀ x ∈ l₁, realBlockExponent x = r) →
      RealInjectiveIntertwinerExists n (pre ++ l₁) (pre ++ l₂) := by
  induction h with
  | nil => exact fun pre _ _ => RealInjectiveIntertwinerExists.refl n _
  | cons x _ ih =>
      intro pre hr ht
      have h := ih (pre ++ [x]) (by simpa using hr) fun y hy => ht y (List.mem_cons_of_mem x hy)
      simpa using h
  | swap x y l =>
      intro pre hr ht
      have hx := ht x (by simp)
      have hy := ht y (by simp)
      exact realUnlinkedSwap n pre l y x hr (le_of_eq (by rw [hx, hy]))
        (areRealBlocksUnlinked_of_eq (by rw [hx, hy]))
  | trans h₁₂ _ ih₁ ih₂ =>
      intro pre hr ht
      refine (ih₁ pre hr ht).trans (ih₂ pre ?_ fun y hy => ht y (h₁₂.symm.subset hy))
      rw [← realRank_perm (h₁₂.append_left pre)]
      exact hr

/-- The scalar commutant is invariant under permutations of tied lists. -/
theorem hasScalarCommutant_perm {n : ℕ} {r : ℝ} {ds es : List RealBlock} (h : ds.Perm es)
    (hr : realRank ds = n) (ht : ∀ x ∈ ds, realBlockExponent x = r)
    (hds : HasScalarCommutant n ds) : HasScalarCommutant n es :=
  hasScalarCommutant_of_twoWay (realInjectiveIntertwinerExists_perm h [] hr ht)
    (realInjectiveIntertwinerExists_perm h.symm [] (by rw [List.nil_append, ← realRank_perm h]; exact hr)
      fun x hx => ht x (h.symm.subset hx))
    hds

/-! ## Character lists with the odd characters last -/

theorem neg_one_pow_fin_two (e : Fin 2) : (-1 : ℂ) ^ e.val = -1 ↔ e = 1 := by
  fin_cases e <;> norm_num

theorem realPositionCharacter_map_character_neg_one (cs : List RealCharacterData) (i : ℕ)
    (hi : i < cs.length) :
    realPositionCharacter (cs.map RealBlock.character) i (-1) = (-1) ^ (cs[i].parity.val) := by
  rw [RealJacquetFrobenius.realPositionCharacter_map_character cs i hi, cs[i].character_eq]
  simp

theorem mem_signSet_iff {n : ℕ} {cs : List RealCharacterData} (hn : cs.length = n) (l : Fin n) :
    l ∈ signSet n (cs.map RealBlock.character) ↔
      (cs[(l : ℕ)]'(lt_of_lt_of_eq l.2 hn.symm)).parity = 1 := by
  simp only [signSet, mem_filter, mem_univ, true_and]
  rw [realPositionCharacter_map_character_neg_one cs l (lt_of_lt_of_eq l.2 hn.symm)]
  exact neg_one_pow_fin_two _

/-- If the parities weakly increase along `cs`, the odd positions form a bottom segment. -/
theorem isBottom_signSet {n : ℕ} {cs : List RealCharacterData} (hn : cs.length = n)
    (hsort : cs.Pairwise fun a b => a.parity.val ≤ b.parity.val) :
    IsBottom (signSet n (cs.map RealBlock.character)) := by
  intro i j hij hi
  rw [mem_signSet_iff hn] at hi ⊢
  rcases hij.lt_or_eq with h | h
  · have h1 := List.pairwise_iff_getElem.mp hsort i j (lt_of_lt_of_eq i.2 hn.symm)
      (lt_of_lt_of_eq j.2 hn.symm) h
    rw [hi] at h1
    have h2 := (cs[(j : ℕ)]'(lt_of_lt_of_eq j.2 hn.symm)).parity.isLt
    exact Fin.ext (by simp only [Fin.val_one] at h1 ⊢; omega)
  · subst h
    exact hi

theorem realPositionExponent_map_character_re (r : ℝ) :
    ∀ (cs : List RealCharacterData), (∀ c ∈ cs, c.exponent.re = r) →
      ∀ i < cs.length, (realPositionExponent (cs.map RealBlock.character) i).re = r
  | [], _, i, hi => by simp at hi
  | c :: cs, h, 0, _ => by simpa [realPositionExponent] using h c (by simp)
  | c :: cs, h, i + 1, hi => by
      simp only [List.map_cons, realPositionExponent]
      exact realPositionExponent_map_character_re r cs (fun c' hc' => h c' (by simp [hc'])) i
        (by simpa using hi)

/-- **Assembly for a sorted character list.** -/
theorem hasScalarCommutant_sorted (hS : RealSphericalCyclicStatement) {n : ℕ} (r : ℝ)
    (cs : List RealCharacterData) (hn : cs.length = n) (hr : ∀ c ∈ cs, c.exponent.re = r)
    (hsort : cs.Pairwise fun a b => a.parity.val ≤ b.parity.val) :
    HasScalarCommutant n (cs.map RealBlock.character) := by
  have hds : IsPrincipal (cs.map RealBlock.character) := isPrincipal_map_character cs
  have hR := isBottom_signSet hn hsort
  refine hasScalarCommutant_of_cyclic hds fun W _ hWL hvec =>
    eq_top_of_sphCyclic hds hR (fun W' hW' hW'L => ?_) W hWL hvec
  refine hS n (sphList n (cs.map RealBlock.character) (signSet n (cs.map RealBlock.character)))
    (sphList_length _) (sphList_parity _) ?_ (sphVec _) (sphVec_fixed _) (sphVec_ne_zero _) W'
    hW' hW'L
  unfold Langlands.Archimedean.IsRealLanglandsOrdered sphList
  rw [List.pairwise_map, List.pairwise_ofFn]
  intro i j hij
  change (shiftExp n _ _ j).re ≤ (shiftExp n _ _ i).re
  have hi := realPositionExponent_map_character_re r cs hr i (lt_of_lt_of_eq i.2 hn.symm)
  have hj := realPositionExponent_map_character_re r cs hr j (lt_of_lt_of_eq j.2 hn.symm)
  simp only [shiftExp, Complex.sub_re, hi, hj]
  by_cases hjR : j ∈ signSet n (cs.map RealBlock.character)
  · by_cases hiR : i ∈ signSet n (cs.map RealBlock.character)
    · simp [hiR, hjR]
    · simp [hiR, hjR]
  · have hiR : i ∉ signSet n (cs.map RealBlock.character) := fun hiR => hjR (hR i j hij.le hiR)
    simp [hiR, hjR]

/-! ## Expanding blocks of weight zero -/

/-- The characters of a non-discrete block, as in `realBlockExpand`. -/
def blockChars : RealBlock → List RealCharacterData
  | .character c => [c]
  | .induced d =>
      [RealJacquetFrobenius.charData 1 d.exponent, RealJacquetFrobenius.charData 0 d.exponent]

theorem realBlockExpand_eq {x : RealBlock} (hx : ¬ IsRealDiscreteSeriesBlock x) :
    realBlockExpand x = (blockChars x).map RealBlock.character := by
  rcases x with c | d
  · rfl
  · simp only [IsRealDiscreteSeriesBlock, ne_eq, not_not] at hx
    simp [realBlockExpand, blockChars, hx]

theorem flatMap_expand_eq : ∀ ds : List RealBlock, (∀ x ∈ ds, ¬ IsRealDiscreteSeriesBlock x) →
    ds.flatMap realBlockExpand = (ds.flatMap blockChars).map RealBlock.character
  | [], _ => rfl
  | x :: ds, h => by
      rw [List.flatMap_cons, List.flatMap_cons, List.map_append,
        realBlockExpand_eq (h x (by simp)), flatMap_expand_eq ds fun y hy => h y (by simp [hy])]

theorem exponent_re_of_mem_blockChars {x : RealBlock} {c : RealCharacterData}
    (hc : c ∈ blockChars x) : c.exponent.re = realBlockExponent x := by
  rcases x with c' | d
  · simp only [blockChars, List.mem_singleton] at hc
    subst hc
    rfl
  · simp only [blockChars, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> rfl

/-- Sorting a list of characters: the even characters first, then the odd ones. -/
def sortParity (cs : List RealCharacterData) : List RealCharacterData :=
  cs.filter (fun c => decide (c.parity = 0)) ++ cs.filter (fun c => !decide (c.parity = 0))

theorem sortParity_perm (cs : List RealCharacterData) : (sortParity cs).Perm cs :=
  List.filter_append_perm _ cs

theorem pairwise_sortParity (cs : List RealCharacterData) :
    (sortParity cs).Pairwise fun a b => a.parity.val ≤ b.parity.val := by
  have h0 : ∀ a ∈ cs.filter (fun c => decide (c.parity = 0)), a.parity.val = 0 := by
    intro a ha
    simp only [List.mem_filter, decide_eq_true_eq] at ha
    rw [ha.2]
    rfl
  have h1 : ∀ a ∈ cs.filter (fun c => !decide (c.parity = 0)), a.parity.val = 1 := by
    intro a ha
    simp only [List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not] at ha
    have h2 := a.parity.isLt
    have h3 : a.parity.val ≠ 0 := fun h => ha.2 (Fin.ext h)
    omega
  rw [sortParity, List.pairwise_append]
  refine ⟨List.pairwise_of_forall_mem_list fun a ha b _ => ?_,
    List.pairwise_of_forall_mem_list fun a _ b hb => ?_, fun a ha b hb => ?_⟩
  · rw [h0 a ha]
    exact Nat.zero_le _
  · rw [h1 b hb]
    have := a.parity.isLt
    omega
  · rw [h0 a ha]
    exact Nat.zero_le _

/-! ## The scalar commutant for tied lists without discrete series -/

/-- **Tied lists without discrete-series block**, given the spherical cyclicity input. -/
theorem hasScalarCommutant_of_nondiscrete (hS : RealSphericalCyclicStatement) (n : ℕ)
    (ds : List RealBlock) (hrank : realRank ds = n)
    (htied : ∀ x ∈ ds, ∀ y ∈ ds, realBlockExponent x = realBlockExponent y)
    (hnd : ∀ x ∈ ds, ¬ IsRealDiscreteSeriesBlock x) : HasScalarCommutant n ds := by
  obtain ⟨r, hr⟩ : ∃ r : ℝ, ∀ x ∈ ds, realBlockExponent x = r := by
    rcases ds with _ | ⟨x₀, ds'⟩
    · exact ⟨0, by simp⟩
    · exact ⟨realBlockExponent x₀, fun x hx => htied x hx x₀ (by simp)⟩
  have hexp : ds.flatMap realBlockExpand = (ds.flatMap blockChars).map RealBlock.character :=
    flatMap_expand_eq ds hnd
  have hmod : realStandardModule n ds =
      realStandardModule n ((ds.flatMap blockChars).map RealBlock.character) := by
    rw [← hexp]
    exact realStandardModule_append_flatMap_expand n ds []
  have hcs : ∀ c ∈ ds.flatMap blockChars, c.exponent.re = r := by
    intro c hc
    obtain ⟨x, hx, hcx⟩ := List.mem_flatMap.mp hc
    rw [exponent_re_of_mem_blockChars hcx, hr x hx]
  have hlen : (ds.flatMap blockChars).length = n := by
    rw [← realRank_map_character, ← hexp, realRank_flatMap_expand, hrank]
  have hperm := sortParity_perm (ds.flatMap blockChars)
  have hsorted : HasScalarCommutant n ((sortParity (ds.flatMap blockChars)).map
      RealBlock.character) :=
    hasScalarCommutant_sorted hS r _ (by rw [hperm.length_eq, hlen])
      (fun c hc => hcs c (hperm.subset hc)) (pairwise_sortParity _)
  have hchar : HasScalarCommutant n ((ds.flatMap blockChars).map RealBlock.character) := by
    refine hasScalarCommutant_perm (r := r) (hperm.map RealBlock.character) ?_ ?_ hsorted
    · rw [realRank_map_character, hperm.length_eq, hlen]
    · intro x hx
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
      exact hcs c (hperm.subset hc)
  exact hasScalarCommutant_of_twoWay ((RealInjectiveIntertwinerExists.refl n _).of_eq rfl hmod.symm)
    ((RealInjectiveIntertwinerExists.refl n _).of_eq rfl hmod) hchar

end RealTiedScalarAssembly

/-- The reduction of the tied case without discrete-series blocks to spherical cyclicity:
`RealSphericalCyclicStatement` implies `RealTiedNondiscreteScalarCommutantStatement`. -/
def RealTiedNondiscreteReductionStatement : Prop :=
  RealSphericalCyclicStatement → RealTiedNondiscreteScalarCommutantStatement

/-- Proof of the reduction `RealTiedNondiscreteReductionStatement`. -/
theorem realTiedNondiscreteReduction : RealTiedNondiscreteReductionStatement :=
  fun hS n ds hrank htied hnd =>
    RealTiedScalarAssembly.hasScalarCommutant_of_nondiscrete hS n ds hrank htied hnd

end Langlands.Archimedean
