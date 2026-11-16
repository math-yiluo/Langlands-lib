import Langlands.Representation.Archimedean.RealUnlinkedSwapReduction
import Langlands.Representation.Archimedean.ComplexJacquetBorel

/-!
# The linked Jacquet functional from pairs of blocks, swaps and induction in stages

`RealLinkedJacquetFunctionalExists n ds` says that the `O(n)`-finite functions of the standard
module of `ds` carry a nonzero real Jacquet functional `ℓ` with exponents `a` and signs `e`, a
position `p` with `p + 1 < n` and `k : ℕ` such that `a_p - a_{p+1} = 1 - k` and
`ℓ ∘ π(E_{p+1,p})^k = 0`.

This file reduces the existence of such a functional for every Langlands-ordered list with a
linked pair of Mœglin data to

* `RealLinkedJacquetFunctionalInStagesStatement` (induction in stages from a sublist of blocks,
  twisted by `|det|^c` with `c = (rank post - rank pre)/2`);
* `RealUnlinkedSwapStatement` (Library: injective swaps of adjacent unlinked blocks);
* `RealSwapInjectiveIntertwinerSurjectiveStatement` (such injective swaps are surjective);
* `RealPairLinkedJacquetFunctionalStatement` (the case of two linked nondegenerate blocks),
  which is split into four statements by the kinds of the two blocks.

The proof (`realLinkedJacquetFunctionalReduction`) expands induction blocks of weight `0`,
chooses a linked pair `x, z` such that no block between them is linked to `z`, moves `z` next
to `x` by swaps, and restricts to the pair `[x, z]`.
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

/-! ## The conclusion -/

/-- The `O(n)`-finite functions of the standard module of `ds` carry a nonzero real Jacquet
functional `ℓ` with exponents `a` and signs `e`, with a position `p`, `p + 1 < n`, and `k : ℕ`
such that `a_p - a_{p+1} = 1 - k` and `ℓ(π(E_{p+1,p})^k v) = 0` for every `v`. Here
`π(E_{p+1,p})` is the action of `1 ⊗ E_{p+1,p}` through `realStandardLie n ds`. -/
def RealLinkedJacquetFunctionalExists (n : ℕ) (ds : List RealBlock) : Prop :=
  ∃ (ℓ : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) →ₗ[ℂ] ℂ)
    (a : Fin n → ℂ) (e : Fin n → Fin 2) (p k : ℕ) (hp : p + 1 < n),
    ℓ ≠ 0 ∧ IsRealJacquetFunctional n (realStandardRep n ds) (realStandardLie n ds) ℓ a e ∧
      a ⟨p, Nat.lt_of_succ_lt hp⟩ - a ⟨p + 1, hp⟩ = 1 - (k : ℂ) ∧
      ∀ v : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n),
        ℓ ((realStandardLie n ds
          (1 ⊗ₜ Matrix.single (⟨p + 1, hp⟩ : Fin n) ⟨p, Nat.lt_of_succ_lt hp⟩ (1 : ℝ)) ^ k)
            v) = 0

/-! ## Twisting blocks -/

/-- The real block `x` twisted by `|det|^c`: the exponent `t` of the block becomes `t + c`;
the parity of a character block and the weight of an induction block stay. -/
def realBlockTwist (c : ℝ) : RealBlock → RealBlock
  | .character d => .character (RealJacquetFrobenius.charData d.parity (d.exponent + c))
  | .induced d => .induced (characterOfParams d.weight (d.exponent + c))

@[simp]
theorem realBlockTwist_rank (c : ℝ) (x : RealBlock) : (realBlockTwist c x).rank = x.rank := by
  cases x <;> rfl

theorem realRank_map_realBlockTwist (c : ℝ) (l : List RealBlock) :
    realRank (l.map (realBlockTwist c)) = realRank l := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [List.map_cons, realRank_cons, realRank_cons, ih, realBlockTwist_rank]

theorem realBlockExponent_twist (c : ℝ) (x : RealBlock) :
    realBlockExponent (realBlockTwist c x) = realBlockExponent x + c := by
  cases x <;> simp [realBlockTwist, realBlockExponent, RealJacquetFrobenius.charData]

theorem isRealBlockNondegenerate_twist (c : ℝ) (x : RealBlock) :
    IsRealBlockNondegenerate (realBlockTwist c x) ↔ IsRealBlockNondegenerate x := by
  cases x <;> simp [realBlockTwist, IsRealBlockNondegenerate]

/-- A Mœglin datum twisted by `|·|^c`: the exponent `s` becomes `s + c`. -/
def MoeglinDatum.twist (c : ℂ) : MoeglinDatum → MoeglinDatum
  | .character ε s => .character ε (s + c)
  | .discrete p s => .discrete p (s + c)

/-- Linkedness only depends on differences of exponents. -/
theorem MoeglinDatum.isLinked_twist (c : ℂ) (a b : MoeglinDatum) :
    (a.twist c).IsLinked (b.twist c) ↔ a.IsLinked b := by
  cases a <;> cases b <;>
    simp only [MoeglinDatum.twist, MoeglinDatum.IsLinked, add_sub_add_right_eq_sub]

theorem realBlockMoeglinData_twist (c : ℝ) (x : RealBlock) :
    realBlockMoeglinData (realBlockTwist c x) =
      (realBlockMoeglinData x).map (MoeglinDatum.twist c) := by
  rcases x with d | d
  · simp [realBlockTwist, realBlockMoeglinData, MoeglinDatum.twist,
      RealJacquetFrobenius.charData]
  · by_cases hw : d.weight = 0 <;>
      simp [realBlockTwist, realBlockMoeglinData, hw, MoeglinDatum.twist]

theorem areRealBlocksUnlinked_twist (c : ℝ) (x y : RealBlock) :
    AreRealBlocksUnlinked (realBlockTwist c x) (realBlockTwist c y) ↔
      AreRealBlocksUnlinked x y := by
  simp only [AreRealBlocksUnlinked, realBlockMoeglinData_twist, List.mem_map,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, MoeglinDatum.isLinked_twist]

/-! ## The statements -/

/-- **Induction in stages.** Let `pre ++ core ++ post` be a list of real blocks of total rank
`n`, and let `core'` be `core` twisted by `|det|^c` with `c = (rank post - rank pre)/2`. If the
standard module of `core'` on `GL_r(ℝ)`, `r = realRank core`, carries a functional as in
`RealLinkedJacquetFunctionalExists`, so does the standard module of `pre ++ core ++ post` on
`GL_n(ℝ)`. (The expected functional is `f ↦ ℓ'(g ↦ f(diag(1, g, 1)))`; restriction to the
block `GL_r(ℝ)` at the positions of `core` maps the standard module of `pre ++ core ++ post`
onto that of `core'`, the twist coming from the modulus characters.) -/
def RealLinkedJacquetFunctionalInStagesStatement : Prop :=
  ∀ (n : ℕ) (pre core post : List RealBlock), realRank (pre ++ core ++ post) = n →
    RealLinkedJacquetFunctionalExists (realRank core)
        (core.map (realBlockTwist (((realRank post : ℝ) - (realRank pre : ℝ)) / 2))) →
      RealLinkedJacquetFunctionalExists n (pre ++ core ++ post)

/-- **Injective swaps are surjective.** For lists `pre`, `post` and blocks `x`, `y` of total
rank `n`, every injective `(𝔤, K)`-intertwiner from the `O(n)`-finite functions of the
standard module of `pre ++ x :: y :: post` to those of `pre ++ y :: x :: post` is surjective.
(The two modules have the same `O(n)`-multiplicities, which are finite.) -/
def RealSwapInjectiveIntertwinerSurjectiveStatement : Prop :=
  ∀ (n : ℕ) (pre post : List RealBlock) (x y : RealBlock)
    (T : kFiniteFunctions (realStandardModule n (pre ++ x :: y :: post)) (unitaryCompact ℝ n)
      →ₗ[ℂ] kFiniteFunctions (realStandardModule n (pre ++ y :: x :: post)) (unitaryCompact ℝ n)),
    realRank (pre ++ x :: y :: post) = n → Function.Injective T →
      IsRealStandardIntertwiner n (realStandardRep n (pre ++ y :: x :: post))
        (realStandardLie n (pre ++ y :: x :: post)) (pre ++ x :: y :: post) T →
        Function.Surjective T

/-- **Two linked blocks.** For nondegenerate real blocks `x`, `z` (characters, or induction
blocks of nonzero weight) with `Re t(z) ≤ Re t(x)` and a linked pair of Mœglin data, the
standard module of `[x, z]` on `GL_r(ℝ)`, `r = realRank [x, z]`, carries a functional as in
`RealLinkedJacquetFunctionalExists`. -/
def RealPairLinkedJacquetFunctionalStatement : Prop :=
  ∀ x z : RealBlock, IsRealBlockNondegenerate x → IsRealBlockNondegenerate z →
    realBlockExponent z ≤ realBlockExponent x → ¬ AreRealBlocksUnlinked x z →
      RealLinkedJacquetFunctionalExists (realRank [x, z]) [x, z]

/-- Two linked characters `c`, `d` with `Re t(d) ≤ Re t(c)`, on `GL₂(ℝ)`. -/
def RealCharacterPairLinkedJacquetFunctionalStatement : Prop :=
  ∀ c d : RealCharacterData,
    realBlockExponent (RealBlock.character d) ≤ realBlockExponent (RealBlock.character c) →
      ¬ AreRealBlocksUnlinked (RealBlock.character c) (RealBlock.character d) →
        RealLinkedJacquetFunctionalExists 2 [RealBlock.character c, RealBlock.character d]

/-- An induction block `d` of nonzero weight and a character `c` linked to it, with
`Re t(c) ≤ Re t(d)`, on `GL₃(ℝ)`. -/
def RealInducedCharacterLinkedJacquetFunctionalStatement : Prop :=
  ∀ (d : ComplexCharacterData) (c : RealCharacterData), d.weight ≠ 0 →
    realBlockExponent (RealBlock.character c) ≤ realBlockExponent (RealBlock.induced d) →
      ¬ AreRealBlocksUnlinked (RealBlock.induced d) (RealBlock.character c) →
        RealLinkedJacquetFunctionalExists 3 [RealBlock.induced d, RealBlock.character c]

/-- A character `c` and an induction block `d` of nonzero weight linked to it, with
`Re t(d) ≤ Re t(c)`, on `GL₃(ℝ)`. -/
def RealCharacterInducedLinkedJacquetFunctionalStatement : Prop :=
  ∀ (c : RealCharacterData) (d : ComplexCharacterData), d.weight ≠ 0 →
    realBlockExponent (RealBlock.induced d) ≤ realBlockExponent (RealBlock.character c) →
      ¬ AreRealBlocksUnlinked (RealBlock.character c) (RealBlock.induced d) →
        RealLinkedJacquetFunctionalExists 3 [RealBlock.character c, RealBlock.induced d]

/-- Two linked induction blocks `d`, `e` of nonzero weights with `Re t(e) ≤ Re t(d)`, on
`GL₄(ℝ)`. -/
def RealInducedInducedLinkedJacquetFunctionalStatement : Prop :=
  ∀ d e : ComplexCharacterData, d.weight ≠ 0 → e.weight ≠ 0 →
    realBlockExponent (RealBlock.induced e) ≤ realBlockExponent (RealBlock.induced d) →
      ¬ AreRealBlocksUnlinked (RealBlock.induced d) (RealBlock.induced e) →
        RealLinkedJacquetFunctionalExists 4 [RealBlock.induced d, RealBlock.induced e]

/-- The four kinds of pairs give `RealPairLinkedJacquetFunctionalStatement`. -/
theorem realPairLinkedJacquetFunctional_of_kinds
    (hCC : RealCharacterPairLinkedJacquetFunctionalStatement)
    (hIC : RealInducedCharacterLinkedJacquetFunctionalStatement)
    (hCI : RealCharacterInducedLinkedJacquetFunctionalStatement)
    (hII : RealInducedInducedLinkedJacquetFunctionalStatement) :
    RealPairLinkedJacquetFunctionalStatement := by
  intro x z hx hz hexp hun
  rcases x with c | d <;> rcases z with c' | e
  · exact hCC c c' hexp hun
  · exact hCI c e hz hexp hun
  · exact hIC d c' hx hexp hun
  · exact hII d e hx hz hexp hun

/-- **The reduction.** Induction in stages, unlinked swaps, surjectivity of injective swaps and
the case of two blocks give a functional as in `RealLinkedJacquetFunctionalExists` for every
Langlands-ordered list of real blocks with a linked pair of Mœglin data. -/
def RealLinkedJacquetFunctionalReductionStatement : Prop :=
  RealLinkedJacquetFunctionalInStagesStatement → RealUnlinkedSwapStatement →
    RealSwapInjectiveIntertwinerSurjectiveStatement → RealPairLinkedJacquetFunctionalStatement →
      ∀ (n : ℕ) (ds : List RealBlock), realRank ds = n → IsRealLanglandsOrdered ds →
        ¬ IsRealMoeglinUnlinked ds → RealLinkedJacquetFunctionalExists n ds

/-! ## Transfer along surjective intertwiners -/

/-- There is a surjective `(𝔤, K)`-intertwiner from the `O(n)`-finite functions of the
standard module of `ds` to those of the standard module of `es`. -/
def RealSurjectiveIntertwinerExists (n : ℕ) (ds es : List RealBlock) : Prop :=
  ∃ T : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) →ₗ[ℂ]
      kFiniteFunctions (realStandardModule n es) (unitaryCompact ℝ n),
    Function.Surjective T ∧
      IsRealStandardIntertwiner n (realStandardRep n es) (realStandardLie n es) ds T

theorem RealSurjectiveIntertwinerExists.refl (n : ℕ) (ds : List RealBlock) :
    RealSurjectiveIntertwinerExists n ds ds :=
  ⟨LinearMap.id, Function.surjective_id, isRealStandardIntertwiner_id n ds⟩

theorem RealSurjectiveIntertwinerExists.trans {n : ℕ} {ds es fs : List RealBlock}
    (h₁ : RealSurjectiveIntertwinerExists n ds es) (h₂ : RealSurjectiveIntertwinerExists n es fs) :
    RealSurjectiveIntertwinerExists n ds fs := by
  obtain ⟨T₁, hs₁, h₁⟩ := h₁
  obtain ⟨T₂, hs₂, h₂⟩ := h₂
  exact ⟨T₂ ∘ₗ T₁, hs₂.comp hs₁, h₁.comp_standard h₂⟩

/-- Equal standard modules give a bijective intertwiner, the identity on functions. -/
theorem RealSurjectiveIntertwinerExists.of_eq {n : ℕ} {ds es : List RealBlock}
    (h : realStandardModule n ds = realStandardModule n es) :
    RealSurjectiveIntertwinerExists n ds es := by
  have hK : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) =
      kFiniteFunctions (realStandardModule n es) (unitaryCompact ℝ n) := by rw [h]
  obtain ⟨e, he⟩ := exists_linearEquiv_coe_eq hK
  refine ⟨e.toLinearMap, e.surjective, fun k f => ?_, fun X f => ?_⟩
  · refine ⟨rightTranslation_mem_kFiniteFunctions_realStandardModule n ds f.2 k.2, ?_⟩
    apply Subtype.ext
    rw [LinearEquiv.coe_coe, he, realStandardRep_apply_coe]
    change _ = Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ) _
      ((e f : kFiniteFunctions (realStandardModule n es) (unitaryCompact ℝ n)) :
        Langlands.GeneralLinear n ℝ → ℂ)
    rw [he]
    have hk : (Unitary.toUnits
        (⟨((k : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ), k.2⟩ :
          Matrix.unitaryGroup (Fin n) ℝ) : Langlands.GeneralLinear n ℝ) =
        (k : Langlands.GeneralLinear n ℝ) :=
      Units.ext rfl
    rw [hk]
  · refine ⟨rightDerivative_mem_kFiniteFunctions_realStandardModule n ds f.2 X, ?_⟩
    apply Subtype.ext
    rw [LinearEquiv.coe_coe, he, realStandardLie_one_tmul_apply_coe]
    change _ = rightDerivative (matrixModel ℝ n) X
      ((e f : kFiniteFunctions (realStandardModule n es) (unitaryCompact ℝ n)) :
        Langlands.GeneralLinear n ℝ → ℂ)
    rw [he]

/-- An intertwiner carries powers of `π(Y)` to powers of `π(Y)`. -/
theorem IsRealStandardIntertwiner.map_pow_realStandardLie {n : ℕ} {ds es : List RealBlock}
    {T : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) →ₗ[ℂ]
      kFiniteFunctions (realStandardModule n es) (unitaryCompact ℝ n)}
    (hT : IsRealStandardIntertwiner n (realStandardRep n es) (realStandardLie n es) ds T)
    (Y : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) (k : ℕ)
    (v : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)) :
    T ((realStandardLie n ds Y ^ k) v) = (realStandardLie n es Y ^ k) (T v) := by
  induction k generalizing v with
  | zero => simp only [pow_zero, Module.End.one_apply]
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ih, hT.map_realStandardLie, pow_succ,
      Module.End.mul_apply]

/-- A functional as in `RealLinkedJacquetFunctionalExists` pulls back along a surjective
intertwiner. -/
theorem RealLinkedJacquetFunctionalExists.of_surjective {n : ℕ} {ds es : List RealBlock}
    (hT : RealSurjectiveIntertwinerExists n ds es) (h : RealLinkedJacquetFunctionalExists n es) :
    RealLinkedJacquetFunctionalExists n ds := by
  obtain ⟨T, hs, hT⟩ := hT
  obtain ⟨ℓ, a, e, p, k, hp, hℓ0, ⟨hN, hD⟩, ha, hE⟩ := h
  refine ⟨ℓ ∘ₗ T, a, e, p, k, hp, ?_, ⟨fun X hX v => ?_, fun j v => ⟨?_, ?_⟩⟩, ha, fun v => ?_⟩
  · intro h0
    apply hℓ0
    refine LinearMap.ext fun w => ?_
    obtain ⟨v, rfl⟩ := hs w
    exact LinearMap.congr_fun h0 v
  · rw [LinearMap.comp_apply, hT.map_realStandardLie]
    exact hN X hX (T v)
  · rw [LinearMap.comp_apply, LinearMap.comp_apply, hT.map_realStandardLie]
    exact (hD j (T v)).1
  · rw [LinearMap.comp_apply, LinearMap.comp_apply, hT.map_realStandardRep]
    exact (hD j (T v)).2
  · rw [LinearMap.comp_apply, hT.map_pow_realStandardLie]
    exact hE (T v)

/-! ## Moving a block to the left -/

/-- Moving a block `z` to the left past a list `mid` of blocks with larger or equal real
exponents, none linked to `z`, one swap at a time. -/
theorem realSurjectiveIntertwinerExists_moveLeft (hSw : RealUnlinkedSwapStatement)
    (hSu : RealSwapInjectiveIntertwinerSurjectiveStatement) (n : ℕ) (z : RealBlock) :
    ∀ (mid pre post : List RealBlock), realRank (pre ++ mid ++ z :: post) = n →
      (∀ w ∈ mid, realBlockExponent z ≤ realBlockExponent w ∧ AreRealBlocksUnlinked w z) →
        RealSurjectiveIntertwinerExists n (pre ++ mid ++ z :: post) (pre ++ z :: mid ++ post)
  | [], pre, post, _, _ => by
    simpa using RealSurjectiveIntertwinerExists.refl n (pre ++ z :: post)
  | w :: mid, pre, post, hrank, hmid => by
    have e1 : pre ++ w :: mid ++ z :: post = pre ++ [w] ++ mid ++ z :: post := by simp
    have e2 : pre ++ [w] ++ z :: mid ++ post = pre ++ w :: z :: (mid ++ post) := by simp
    have e3 : pre ++ z :: w :: (mid ++ post) = pre ++ z :: (w :: mid) ++ post := by simp
    rw [e1] at hrank ⊢
    have h1 := realSurjectiveIntertwinerExists_moveLeft hSw hSu n z mid (pre ++ [w]) post hrank
      (fun w' hw' => hmid w' (List.mem_cons_of_mem _ hw'))
    rw [e2] at h1
    have hrank2 : realRank (pre ++ w :: z :: (mid ++ post)) = n := by
      rw [← hrank]
      simp only [Langlands.LocalFactor.Archimedean.realRank_append, realRank_cons,
        realRank_nil]
      omega
    obtain ⟨hwz, hun⟩ := hmid w List.mem_cons_self
    obtain ⟨T, hTi, hT⟩ := hSw n pre (mid ++ post) w z hrank2 hwz hun
    have h2 : RealSurjectiveIntertwinerExists n (pre ++ w :: z :: (mid ++ post))
        (pre ++ z :: w :: (mid ++ post)) :=
      ⟨T, hSu n pre (mid ++ post) w z T hrank2 hTi hT, hT⟩
    rw [e3] at h2
    exact h1.trans h2

/-! ## Expanding blocks of weight zero -/

theorem realStandardModule_append_flatMap_expand (n : ℕ) :
    ∀ (ds pre : List RealBlock),
      realStandardModule n (pre ++ ds) =
        realStandardModule n (pre ++ ds.flatMap realBlockExpand)
  | [], pre => by simp
  | x :: ds, pre => by
    rw [realStandardModule_append_expand n pre ds x, List.flatMap_cons, ← List.append_assoc,
      realStandardModule_append_flatMap_expand n ds (pre ++ realBlockExpand x)]

theorem realRank_flatMap_expand : ∀ ds : List RealBlock,
    realRank (ds.flatMap realBlockExpand) = realRank ds
  | [] => rfl
  | x :: ds => by
    rw [List.flatMap_cons, Langlands.LocalFactor.Archimedean.realRank_append,
      realRank_realBlockExpand, realRank_flatMap_expand ds, realRank_cons]

theorem realBlockExpand_flatMap_moeglinData (x : RealBlock) :
    (realBlockExpand x).flatMap realBlockMoeglinData = realBlockMoeglinData x := by
  rcases x with c | d
  · simp [realBlockExpand]
  · by_cases hw : d.weight = 0
    · simp [realBlockExpand, realBlockMoeglinData, hw, RealJacquetFrobenius.charData]
    · simp [realBlockExpand, hw]

theorem realMoeglinData_flatMap_expand (ds : List RealBlock) :
    realMoeglinData (ds.flatMap realBlockExpand) = realMoeglinData ds := by
  unfold realMoeglinData
  rw [List.flatMap_assoc]
  exact congrArg (List.flatMap · ds) (funext realBlockExpand_flatMap_moeglinData) |>.trans
    (by rfl)

/-- For nondegenerate blocks, being Mœglin-unlinked is pairwise unlinkedness of the blocks. -/
theorem isRealMoeglinUnlinked_of_pairwise {es : List RealBlock}
    (hnd : ∀ b ∈ es, IsRealBlockNondegenerate b) (h : es.Pairwise AreRealBlocksUnlinked) :
    IsRealMoeglinUnlinked es := by
  unfold IsRealMoeglinUnlinked realMoeglinData
  rw [List.pairwise_flatMap]
  refine ⟨fun b hb => ?_, h⟩
  rcases b with c | d
  · simp [realBlockMoeglinData]
  · have hw : d.weight ≠ 0 := hnd _ hb
    simp [realBlockMoeglinData, hw]

/-! ## A linked pair with no block in between linked to the second block -/

theorem exists_split_of_not_pairwise {α : Type*} {R : α → α → Prop} :
    ∀ {l : List α}, ¬ l.Pairwise R →
      ∃ (pre : List α) (x : α) (mid : List α) (y : α) (post : List α),
        l = pre ++ x :: (mid ++ y :: post) ∧ ¬ R x y ∧ ∀ w ∈ mid, R w y
  | [], h => absurd List.Pairwise.nil h
  | a :: l, h => by
    rw [List.pairwise_cons] at h
    by_cases hl : l.Pairwise R
    · have hb : ∃ b ∈ l, ¬ R a b := by
        by_contra hc
        push Not at hc
        exact h ⟨hc, hl⟩
      obtain ⟨b, hb, hab⟩ := hb
      obtain ⟨mid, post, rfl⟩ := List.append_of_mem hb
      exact ⟨[], a, mid, b, post, rfl, hab,
        fun w hw => (List.pairwise_append.1 hl).2.2 w hw b List.mem_cons_self⟩
    · obtain ⟨pre, x, mid, y, post, rfl, hxy, hmid⟩ := exists_split_of_not_pairwise hl
      exact ⟨a :: pre, x, mid, y, post, rfl, hxy, hmid⟩

/-! ## The reduction -/

theorem realLinkedJacquetFunctionalReduction : RealLinkedJacquetFunctionalReductionStatement := by
  intro hSt hSw hSu hPair n ds hrank hord hlink
  -- Expand the induction blocks of weight `0`.
  set es := ds.flatMap realBlockExpand with hes
  have hmod : realStandardModule n ds = realStandardModule n es := by
    simpa using realStandardModule_append_flatMap_expand n ds []
  have hrank_es : realRank es = n := by rw [hes, realRank_flatMap_expand, hrank]
  have hnd : ∀ b ∈ es, IsRealBlockNondegenerate b := by
    intro b hb
    obtain ⟨x, -, hbx⟩ := List.mem_flatMap.1 hb
    exact isRealBlockNondegenerate_of_mem_expand hbx
  have hord_es : es.Pairwise fun a b => realBlockExponent b ≤ realBlockExponent a := by
    rw [hes, List.pairwise_flatMap]
    refine ⟨fun x _ => List.pairwise_of_forall_mem_list fun a ha b hb => ?_, ?_⟩
    · rw [realBlockExponent_of_mem_expand ha, realBlockExponent_of_mem_expand hb]
    · refine hord.imp fun {x y} hxy a ha b hb => ?_
      rw [realBlockExponent_of_mem_expand ha, realBlockExponent_of_mem_expand hb]
      exact hxy
  have hlink_es : ¬ es.Pairwise AreRealBlocksUnlinked := by
    intro h
    apply hlink
    have h' := isRealMoeglinUnlinked_of_pairwise hnd h
    unfold IsRealMoeglinUnlinked at h' ⊢
    rwa [hes, realMoeglinData_flatMap_expand] at h'
  -- A linked pair `x, z` with no block between them linked to `z`.
  obtain ⟨pre, x, mid, z, post, hsplit, hxz, hmid⟩ := exists_split_of_not_pairwise hlink_es
  have hord' := hord_es
  rw [hsplit, List.pairwise_append, List.pairwise_cons, List.pairwise_append] at hord'
  have hzx : realBlockExponent z ≤ realBlockExponent x :=
    hord'.2.1.1 z (List.mem_append_right _ List.mem_cons_self)
  have hzw : ∀ w ∈ mid, realBlockExponent z ≤ realBlockExponent w :=
    fun w hw => hord'.2.1.2.2.2 w hw z List.mem_cons_self
  have hx : IsRealBlockNondegenerate x := hnd x (by rw [hsplit]; simp)
  have hz : IsRealBlockNondegenerate z := hnd z (by rw [hsplit]; simp)
  -- Move `z` next to `x`.
  have e1 : es = pre ++ [x] ++ mid ++ z :: post := by rw [hsplit]; simp
  have e2 : pre ++ [x] ++ z :: mid ++ post = pre ++ [x, z] ++ (mid ++ post) := by simp
  have hrank1 : realRank (pre ++ [x] ++ mid ++ z :: post) = n := by rw [← e1, hrank_es]
  have hmove := realSurjectiveIntertwinerExists_moveLeft hSw hSu n z mid (pre ++ [x]) post
    hrank1 (fun w hw => ⟨hzw w hw, hmid w hw⟩)
  rw [← e1, e2] at hmove
  -- Restrict to the pair `[x, z]`.
  set c : ℝ := ((realRank (mid ++ post) : ℝ) - (realRank pre : ℝ)) / 2 with hc
  have hpair := hPair (realBlockTwist c x) (realBlockTwist c z)
    ((isRealBlockNondegenerate_twist c x).2 hx) ((isRealBlockNondegenerate_twist c z).2 hz)
    (by rw [realBlockExponent_twist, realBlockExponent_twist]; linarith)
    (fun h => hxz ((areRealBlocksUnlinked_twist c x z).1 h))
  have hr : realRank [realBlockTwist c x, realBlockTwist c z] = realRank [x, z] := by
    exact realRank_map_realBlockTwist c [x, z]
  rw [hr] at hpair
  have hrank2 : realRank (pre ++ [x, z] ++ (mid ++ post)) = n := by
    rw [← e2]
    rw [e1] at hrank_es
    rw [← hrank_es]
    simp only [Langlands.LocalFactor.Archimedean.realRank_append, realRank_cons, realRank_nil]
    omega
  have hstage := hSt n pre [x, z] (mid ++ post) hrank2 hpair
  exact RealLinkedJacquetFunctionalExists.of_surjective (RealSurjectiveIntertwinerExists.of_eq hmod)
    (RealLinkedJacquetFunctionalExists.of_surjective hmove hstage)

end Langlands.Archimedean
