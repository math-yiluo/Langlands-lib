import Langlands.LocalFactor.ArchimedeanPairFactor
import Langlands.Representation.Archimedean.RealStandardIrreducibleCriterionReduction
import Langlands.Representation.Archimedean.RealJacquetFrobeniusProof

/-!
# Reduction of unlinked swaps of real blocks to four kinds of pairs

`RealUnlinkedSwapStatement` (module `RealStandardIrreducibleCriterionReduction`) asks for an
injective `(𝔤, K)`-intertwiner exchanging two adjacent unlinked real blocks `x`, `y` with
`Re t(y) ≤ Re t(x)`. This file reduces it to the four statements obtained by fixing the kinds
of `x` and `y`, where an induction block always has nonzero weight:

* `RealCharacterSwapStatement`: two character blocks;
* `RealCharacterInducedSwapStatement`: a character block, then an induction block;
* `RealInducedCharacterSwapStatement`: an induction block, then a character block;
* `RealInducedSwapStatement`: two induction blocks.

An induction block of weight `0` has the same standard module as the two character blocks
`sgn |·|^t`, `|·|^t` (`realStandardModule_append_expand`): the Fourier conditions of weight `0`
are empty and the position characters agree. It also has the same Mœglin data. So the
reduction replaces such a block by these two character blocks and moves the blocks one at a
time (`realUnlinkedSwapReduction`).
-/

noncomputable section

open scoped TensorProduct Matrix

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean
open scoped Matrix.Norms.Operator

-- As in `RealLargeStandardIrreducibleReduction`.
set_option backward.isDefEq.respectTransparency false

/-! ## The four statements -/

/-- **Swapping two unlinked character blocks.** For lists `pre`, `post` and real characters
`a`, `b` with `Re t(b) ≤ Re t(a)` whose Mœglin data are not linked, of total rank `n`, there is
an injective `(𝔤, K)`-intertwiner from the `O(n)`-finite functions of the standard module of
`pre ++ a :: b :: post` to those of `pre ++ b :: a :: post`. -/
def RealCharacterSwapStatement : Prop :=
  ∀ (n : ℕ) (pre post : List RealBlock) (a b : RealCharacterData),
    realRank (pre ++ RealBlock.character a :: RealBlock.character b :: post) = n →
      realBlockExponent (RealBlock.character b) ≤ realBlockExponent (RealBlock.character a) →
        AreRealBlocksUnlinked (RealBlock.character a) (RealBlock.character b) →
          RealInjectiveIntertwinerExists n
            (pre ++ RealBlock.character a :: RealBlock.character b :: post)
            (pre ++ RealBlock.character b :: RealBlock.character a :: post)

/-- **Moving an induction block of nonzero weight before an unlinked character block.** For
lists `pre`, `post`, a real character `a` and a complex character `e` of nonzero weight with
`Re t(e) ≤ Re t(a)` whose Mœglin data are not linked, of total rank `n`, there is an injective
`(𝔤, K)`-intertwiner from the `O(n)`-finite functions of the standard module of
`pre ++ a :: e :: post` to those of `pre ++ e :: a :: post`. -/
def RealCharacterInducedSwapStatement : Prop :=
  ∀ (n : ℕ) (pre post : List RealBlock) (a : RealCharacterData) (e : ComplexCharacterData),
    e.weight ≠ 0 →
      realRank (pre ++ RealBlock.character a :: RealBlock.induced e :: post) = n →
        realBlockExponent (RealBlock.induced e) ≤ realBlockExponent (RealBlock.character a) →
          AreRealBlocksUnlinked (RealBlock.character a) (RealBlock.induced e) →
            RealInjectiveIntertwinerExists n
              (pre ++ RealBlock.character a :: RealBlock.induced e :: post)
              (pre ++ RealBlock.induced e :: RealBlock.character a :: post)

/-- **Moving a character block before an unlinked induction block of nonzero weight.** For
lists `pre`, `post`, a complex character `d` of nonzero weight and a real character `b` with
`Re t(b) ≤ Re t(d)` whose Mœglin data are not linked, of total rank `n`, there is an injective
`(𝔤, K)`-intertwiner from the `O(n)`-finite functions of the standard module of
`pre ++ d :: b :: post` to those of `pre ++ b :: d :: post`. -/
def RealInducedCharacterSwapStatement : Prop :=
  ∀ (n : ℕ) (pre post : List RealBlock) (d : ComplexCharacterData) (b : RealCharacterData),
    d.weight ≠ 0 →
      realRank (pre ++ RealBlock.induced d :: RealBlock.character b :: post) = n →
        realBlockExponent (RealBlock.character b) ≤ realBlockExponent (RealBlock.induced d) →
          AreRealBlocksUnlinked (RealBlock.induced d) (RealBlock.character b) →
            RealInjectiveIntertwinerExists n
              (pre ++ RealBlock.induced d :: RealBlock.character b :: post)
              (pre ++ RealBlock.character b :: RealBlock.induced d :: post)

/-- **Swapping two unlinked induction blocks of nonzero weights.** For lists `pre`, `post` and
complex characters `d`, `e` of nonzero weights with `Re t(e) ≤ Re t(d)` whose Mœglin data are
not linked, of total rank `n`, there is an injective `(𝔤, K)`-intertwiner from the
`O(n)`-finite functions of the standard module of `pre ++ d :: e :: post` to those of
`pre ++ e :: d :: post`. -/
def RealInducedSwapStatement : Prop :=
  ∀ (n : ℕ) (pre post : List RealBlock) (d e : ComplexCharacterData),
    d.weight ≠ 0 → e.weight ≠ 0 →
      realRank (pre ++ RealBlock.induced d :: RealBlock.induced e :: post) = n →
        realBlockExponent (RealBlock.induced e) ≤ realBlockExponent (RealBlock.induced d) →
          AreRealBlocksUnlinked (RealBlock.induced d) (RealBlock.induced e) →
            RealInjectiveIntertwinerExists n
              (pre ++ RealBlock.induced d :: RealBlock.induced e :: post)
              (pre ++ RealBlock.induced e :: RealBlock.induced d :: post)

/-- The four swap statements for fixed kinds of blocks imply `RealUnlinkedSwapStatement`. -/
def RealUnlinkedSwapReductionStatement : Prop :=
  RealCharacterSwapStatement → RealCharacterInducedSwapStatement →
    RealInducedCharacterSwapStatement → RealInducedSwapStatement → RealUnlinkedSwapStatement

/-! ## Transport along equal standard modules -/

/-- A linear equivalence between equal submodules that is the identity on functions. -/
theorem exists_linearEquiv_coe_eq {n : ℕ} {V W : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ)}
    (h : V = W) :
    ∃ e : V ≃ₗ[ℂ] W, ∀ x, ((e x : W) : Langlands.GeneralLinear n ℝ → ℂ) = x :=
  ⟨LinearEquiv.ofEq _ _ h, fun _ => rfl⟩

/-- Injective intertwiners between standard modules only depend on the standard modules as
spaces of functions. -/
theorem RealInjectiveIntertwinerExists.of_eq {n : ℕ} {ds ds' es es' : List RealBlock}
    (hd : realStandardModule n ds = realStandardModule n ds')
    (he : realStandardModule n es = realStandardModule n es')
    (h : RealInjectiveIntertwinerExists n ds es) : RealInjectiveIntertwinerExists n ds' es' := by
  obtain ⟨T, hTi, hT⟩ := h
  have hdK : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) =
      kFiniteFunctions (realStandardModule n ds') (unitaryCompact ℝ n) := by rw [hd]
  have heK : kFiniteFunctions (realStandardModule n es) (unitaryCompact ℝ n) =
      kFiniteFunctions (realStandardModule n es') (unitaryCompact ℝ n) := by rw [he]
  obtain ⟨e₁, he₁⟩ := exists_linearEquiv_coe_eq hdK.symm
  obtain ⟨e₂, he₂⟩ := exists_linearEquiv_coe_eq heK
  refine ⟨e₂.toLinearMap ∘ₗ T ∘ₗ e₁.toLinearMap, e₂.injective.comp (hTi.comp e₁.injective),
    fun k f => ?_, fun X f => ?_⟩
  · obtain ⟨hf, hTf⟩ := hT.1 k (e₁ f)
    have hf' : Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ)
        (k : Langlands.GeneralLinear n ℝ) (f : Langlands.GeneralLinear n ℝ → ℂ) ∈
          kFiniteFunctions (realStandardModule n ds') (unitaryCompact ℝ n) := by
      have h0 := hf
      rw [he₁] at h0
      rwa [hdK] at h0
    refine ⟨hf', Subtype.ext ?_⟩
    have h1 : e₁ ⟨_, hf'⟩ = ⟨_, hf⟩ := Subtype.ext (by simp only [he₁])
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, he₂, h1, hTf,
      realStandardRep_apply_coe]
  · obtain ⟨hf, hTf⟩ := hT.2 X (e₁ f)
    have hf' : rightDerivative (matrixModel ℝ n) X (f : Langlands.GeneralLinear n ℝ → ℂ) ∈
          kFiniteFunctions (realStandardModule n ds') (unitaryCompact ℝ n) := by
      have h0 := hf
      rw [he₁] at h0
      rwa [hdK] at h0
    refine ⟨hf', Subtype.ext ?_⟩
    have h1 : e₁ ⟨_, hf'⟩ = ⟨_, hf⟩ := Subtype.ext (by simp only [he₁])
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, he₂, h1, hTf,
      realStandardLie_one_tmul_apply_coe]

/-! ## Induction blocks of weight zero -/

/-- The position characters of `pre ++ A` and `pre ++ B` agree when those of `A` and `B`
agree. -/
theorem realPositionCharacter_append_congr {A B : List RealBlock}
    (h : ∀ p, realPositionCharacter A p = realPositionCharacter B p) :
    ∀ (pre : List RealBlock) (p : ℕ),
      realPositionCharacter (pre ++ A) p = realPositionCharacter (pre ++ B) p
  | [], p => h p
  | .character _ :: _, 0 => rfl
  | .character _ :: pre, p + 1 => realPositionCharacter_append_congr h pre p
  | .induced _ :: _, 0 => rfl
  | .induced _ :: _, 1 => rfl
  | .induced _ :: pre, p + 2 => realPositionCharacter_append_congr h pre p

/-- A reflexive relation between the induction blocks of `A` and `B` at every position passes
to `pre ++ A` and `pre ++ B`. -/
theorem realInducedBlockAt_append_congr
    {R : Option ComplexCharacterData → Option ComplexCharacterData → Prop}
    (hR : ∀ o, R o o) {A B : List RealBlock}
    (h : ∀ p, R (realInducedBlockAt A p) (realInducedBlockAt B p)) :
    ∀ (pre : List RealBlock) (p : ℕ),
      R (realInducedBlockAt (pre ++ A) p) (realInducedBlockAt (pre ++ B) p)
  | [], p => h p
  | .character _ :: _, 0 => hR _
  | .character _ :: pre, p + 1 => realInducedBlockAt_append_congr hR h pre p
  | .induced _ :: _, 0 => hR _
  | .induced _ :: _, 1 => hR _
  | .induced _ :: pre, p + 2 => realInducedBlockAt_append_congr hR h pre p

/-- The relation between the induction blocks of two lists that makes their standard modules
equal: every induction block of the second list is one of the first, and every induction block
of nonzero weight of the first is one of the second. -/
def InducedBlockRelation (o o' : Option ComplexCharacterData) : Prop :=
  (∀ d, o' = some d → o = some d) ∧ (∀ d, o = some d → d.weight ≠ 0 → o' = some d)

theorem inducedBlockRelation_refl (o : Option ComplexCharacterData) :
    InducedBlockRelation o o :=
  ⟨fun _ h => h, fun _ h _ => h⟩

/-- Two lists with the same position characters and related induction blocks have the same
standard module: Fourier conditions of weight `0` are empty. -/
theorem realStandardModule_eq_of_inducedBlockRelation (n : ℕ) {ds es : List RealBlock}
    (hχ : ∀ p, realPositionCharacter ds p = realPositionCharacter es p)
    (hR : ∀ p, InducedBlockRelation (realInducedBlockAt ds p) (realInducedBlockAt es p)) :
    realStandardModule n ds = realStandardModule n es := by
  have hχ' : realPositionCharacter ds = realPositionCharacter es := funext hχ
  ext f
  rw [mem_realStandardModule_iff, mem_realStandardModule_iff, hχ']
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun p d hd k hk g => h2 p d ((hR p).1 d hd) k hk g⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun p d hd k hk g => ?_⟩
    by_cases hw : d.weight = 0
    · rw [hw, abs_zero] at hk
      exact absurd hk (not_lt.2 (abs_nonneg k))
    · exact h2 p d ((hR p).2 d hd hw) k hk g

/-- The expansion of a real block: an induction block of weight `0` and exponent `t` becomes
the two character blocks `sgn |·|^t`, `|·|^t`; every other block stays. -/
def realBlockExpand : RealBlock → List RealBlock
  | .character c => [.character c]
  | .induced d =>
      if d.weight = 0 then
        [.character (RealJacquetFrobenius.charData 1 d.exponent),
          .character (RealJacquetFrobenius.charData 0 d.exponent)]
      else [.induced d]

/-- A block is nondegenerate when it is a character block or an induction block of nonzero
weight. -/
def IsRealBlockNondegenerate : RealBlock → Prop
  | .character _ => True
  | .induced d => d.weight ≠ 0

/-- Expanding a block does not change the standard module. -/
theorem realStandardModule_append_expand (n : ℕ) (pre post : List RealBlock) (x : RealBlock) :
    realStandardModule n (pre ++ x :: post) =
      realStandardModule n (pre ++ realBlockExpand x ++ post) := by
  rcases x with c | d
  · simp [realBlockExpand]
  by_cases hw : d.weight = 0
  · simp only [realBlockExpand, hw, ↓reduceIte, List.cons_append, List.nil_append,
      List.append_assoc]
    apply realStandardModule_eq_of_inducedBlockRelation
    · refine realPositionCharacter_append_congr (fun p => ?_) pre
      rcases p with _ | _ | p
      · funext x
        simp only [realPositionCharacter, realInducedFirstCharacter,
          RealJacquetFrobenius.charData_character_apply, RealJacquetFrobenius.charFun, hw,
          Int.natAbs_zero, Nat.cast_zero, zero_div, add_zero, zero_add, Fin.val_one]
      · funext x
        simp only [realPositionCharacter, realInducedSecondCharacter,
          RealJacquetFrobenius.charData_character_apply, RealJacquetFrobenius.charFun, hw,
          Int.natAbs_zero, Nat.cast_zero, zero_div, sub_zero, Fin.val_zero, pow_zero, one_mul]
      · rfl
    · refine realInducedBlockAt_append_congr inducedBlockRelation_refl (fun p => ?_) pre
      rcases p with _ | _ | p
      · refine ⟨fun d' h => ?_, fun d' h hd' => ?_⟩
        · simp [realInducedBlockAt] at h
        · simp only [realInducedBlockAt, Option.some.injEq] at h
          exact absurd (h ▸ hw) hd'
      · exact inducedBlockRelation_refl _
      · exact inducedBlockRelation_refl _
  · simp [realBlockExpand, hw]

theorem realRank_realBlockExpand (x : RealBlock) : realRank (realBlockExpand x) = x.rank := by
  rcases x with c | d
  · simp [realBlockExpand, realRank]
  · by_cases hw : d.weight = 0 <;> simp [realBlockExpand, realRank, hw, RealBlock.rank]

theorem realBlockExponent_of_mem_expand {x a : RealBlock} (ha : a ∈ realBlockExpand x) :
    realBlockExponent a = realBlockExponent x := by
  rcases x with c | d
  · simp only [realBlockExpand, List.mem_singleton] at ha
    rw [ha]
  · by_cases hw : d.weight = 0
    · simp only [realBlockExpand, hw, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl <;> rfl
    · simp only [realBlockExpand, hw, ↓reduceIte, List.mem_singleton] at ha
      rw [ha]

theorem isRealBlockNondegenerate_of_mem_expand {x a : RealBlock} (ha : a ∈ realBlockExpand x) :
    IsRealBlockNondegenerate a := by
  rcases x with c | d
  · simp only [realBlockExpand, List.mem_singleton] at ha
    rw [ha]
    trivial
  · by_cases hw : d.weight = 0
    · simp only [realBlockExpand, hw, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl <;> trivial
    · simp only [realBlockExpand, hw, ↓reduceIte, List.mem_singleton] at ha
      rw [ha]
      exact hw

theorem mem_realBlockMoeglinData_of_mem_expand {x a : RealBlock} (ha : a ∈ realBlockExpand x)
    {m : MoeglinDatum} (hm : m ∈ realBlockMoeglinData a) : m ∈ realBlockMoeglinData x := by
  rcases x with c | d
  · simp only [realBlockExpand, List.mem_singleton] at ha
    rwa [ha] at hm
  · by_cases hw : d.weight = 0
    · simp only [realBlockExpand, hw, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at ha
      simp only [realBlockMoeglinData, hw, ↓reduceIte, List.mem_cons, List.not_mem_nil,
        or_false]
      rcases ha with rfl | rfl
      · simp only [realBlockMoeglinData, List.mem_singleton] at hm
        exact Or.inl hm
      · simp only [realBlockMoeglinData, List.mem_singleton] at hm
        exact Or.inr hm
    · simp only [realBlockExpand, hw, ↓reduceIte, List.mem_singleton] at ha
      rwa [ha] at hm

theorem areRealBlocksUnlinked_of_mem_expand {x y a b : RealBlock} (hxy : AreRealBlocksUnlinked x y)
    (ha : a ∈ realBlockExpand x) (hb : b ∈ realBlockExpand y) : AreRealBlocksUnlinked a b :=
  fun m hm m' hm' => hxy m (mem_realBlockMoeglinData_of_mem_expand ha hm) m'
    (mem_realBlockMoeglinData_of_mem_expand hb hm')

/-! ## Moving blocks -/

/-- The hypotheses of one swap of nondegenerate blocks. -/
def IsRealSwappable (a b : RealBlock) : Prop :=
  IsRealBlockNondegenerate a ∧ IsRealBlockNondegenerate b ∧
    realBlockExponent b ≤ realBlockExponent a ∧ AreRealBlocksUnlinked a b

/-- The four statements give the swap of any two swappable blocks. -/
theorem realInjectiveIntertwinerExists_swap (hCC : RealCharacterSwapStatement)
    (hCI : RealCharacterInducedSwapStatement) (hIC : RealInducedCharacterSwapStatement)
    (hII : RealInducedSwapStatement) (n : ℕ) (pre post : List RealBlock) (a b : RealBlock)
    (hrank : realRank (pre ++ a :: b :: post) = n) (hab : IsRealSwappable a b) :
    RealInjectiveIntertwinerExists n (pre ++ a :: b :: post) (pre ++ b :: a :: post) := by
  obtain ⟨ha, hb, hexp, hun⟩ := hab
  rcases a with c | d <;> rcases b with c' | e
  · exact hCC n pre post c c' hrank hexp hun
  · exact hCI n pre post c e hb hrank hexp hun
  · exact hIC n pre post d c' ha hrank hexp hun
  · exact hII n pre post d e ha hb hrank hexp hun

/-- Moving a block `a` past a list `l` of blocks, each swappable with `a`, one swap at a
time. -/
theorem realInjectiveIntertwinerExists_moveToEnd'
    (hsw : ∀ (n : ℕ) (pre post : List RealBlock) (a b : RealBlock),
      realRank (pre ++ a :: b :: post) = n → IsRealSwappable a b →
        RealInjectiveIntertwinerExists n (pre ++ a :: b :: post) (pre ++ b :: a :: post))
    (n : ℕ) (a : RealBlock) :
    ∀ (l pre post : List RealBlock), realRank (pre ++ a :: l ++ post) = n →
      (∀ b ∈ l, IsRealSwappable a b) →
        RealInjectiveIntertwinerExists n (pre ++ a :: l ++ post) (pre ++ l ++ a :: post)
  | [], pre, post, _, _ => by
    simpa using RealInjectiveIntertwinerExists.refl n (pre ++ a :: post)
  | b :: l, pre, post, hrank, hl => by
    have e1 : pre ++ a :: (b :: l) ++ post = pre ++ a :: b :: (l ++ post) := by simp
    have e2 : pre ++ [b] ++ a :: l ++ post = pre ++ b :: a :: (l ++ post) := by simp
    have e3 : pre ++ [b] ++ l ++ a :: post = pre ++ (b :: l) ++ a :: post := by simp
    rw [e1] at hrank ⊢
    have h1 : RealInjectiveIntertwinerExists n (pre ++ a :: b :: (l ++ post))
        (pre ++ b :: a :: (l ++ post)) :=
      hsw n pre (l ++ post) a b hrank (hl b List.mem_cons_self)
    have hrank' : realRank (pre ++ [b] ++ a :: l ++ post) = n := by
      rw [e2, ← hrank]
      exact realRank_perm (List.Perm.append_left pre (List.Perm.swap a b _))
    have h2 := realInjectiveIntertwinerExists_moveToEnd' hsw n a l (pre ++ [b]) post hrank'
      (fun c hc => hl c (List.mem_cons_of_mem _ hc))
    rw [e2, e3] at h2
    exact h1.trans h2

/-- Moving a list `X` of blocks past a list `Y`, every block of `X` being swappable with every
block of `Y`. -/
theorem realInjectiveIntertwinerExists_moveList
    (hsw : ∀ (n : ℕ) (pre post : List RealBlock) (a b : RealBlock),
      realRank (pre ++ a :: b :: post) = n → IsRealSwappable a b →
        RealInjectiveIntertwinerExists n (pre ++ a :: b :: post) (pre ++ b :: a :: post))
    (n : ℕ) (Y : List RealBlock) :
    ∀ (X pre post : List RealBlock), realRank (pre ++ X ++ Y ++ post) = n →
      (∀ a ∈ X, ∀ b ∈ Y, IsRealSwappable a b) →
        RealInjectiveIntertwinerExists n (pre ++ X ++ Y ++ post) (pre ++ Y ++ X ++ post)
  | [], pre, post, _, _ => by
    simpa using RealInjectiveIntertwinerExists.refl n (pre ++ Y ++ post)
  | a :: X, pre, post, hrank, hXY => by
    have e1 : pre ++ a :: X ++ Y ++ post = pre ++ [a] ++ X ++ Y ++ post := by simp
    have e2 : pre ++ [a] ++ Y ++ X ++ post = pre ++ a :: Y ++ (X ++ post) := by simp
    have e3 : pre ++ Y ++ a :: (X ++ post) = pre ++ Y ++ a :: X ++ post := by simp
    rw [e1] at hrank ⊢
    have h1 := realInjectiveIntertwinerExists_moveList hsw n Y X (pre ++ [a]) post hrank
      (fun a' ha' b hb => hXY a' (List.mem_cons_of_mem _ ha') b hb)
    have hrank' : realRank (pre ++ a :: Y ++ (X ++ post)) = n := by
      rw [← hrank]
      simp only [Langlands.LocalFactor.Archimedean.realRank_append, realRank_cons, realRank_nil]
      omega
    have h2 := realInjectiveIntertwinerExists_moveToEnd' hsw n a Y pre (X ++ post) hrank'
      (fun b hb => hXY a List.mem_cons_self b hb)
    rw [e2] at h1
    rw [e3] at h2
    exact h1.trans h2

/-! ## The reduction -/

/-- **The reduction.** Expand `x` and `y` into lists `X`, `Y` of nondegenerate blocks with the
same standard modules; every block of `X` is swappable with every block of `Y`; move `X` past
`Y` one swap at a time. -/
theorem realUnlinkedSwapReduction : RealUnlinkedSwapReductionStatement := by
  intro hCC hCI hIC hII n pre post x y hrank hexp hun
  have hsw := realInjectiveIntertwinerExists_swap hCC hCI hIC hII
  have hrank' : realRank (pre ++ realBlockExpand x ++ realBlockExpand y ++ post) = n := by
    rw [← hrank]
    simp only [Langlands.LocalFactor.Archimedean.realRank_append, realRank_cons, realRank_realBlockExpand]
    omega
  have h := realInjectiveIntertwinerExists_moveList hsw n (realBlockExpand y)
    (realBlockExpand x) pre post hrank' (fun a ha b hb =>
      ⟨isRealBlockNondegenerate_of_mem_expand ha, isRealBlockNondegenerate_of_mem_expand hb,
        by rw [realBlockExponent_of_mem_expand ha, realBlockExponent_of_mem_expand hb]
           exact hexp,
        areRealBlocksUnlinked_of_mem_expand hun ha hb⟩)
  refine h.of_eq ?_ ?_
  · rw [← realStandardModule_append_expand n (pre ++ realBlockExpand x) post y,
      ← realStandardModule_append_expand n pre (y :: post) x]
  · rw [← realStandardModule_append_expand n (pre ++ realBlockExpand y) post x,
      ← realStandardModule_append_expand n pre (x :: post) y]

end Langlands.Archimedean
