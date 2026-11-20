import Langlands.Representation.Archimedean.RealLinkedLanglandsQuotientNotLargeProof
import Langlands.Representation.Archimedean.RealInducedCharacterMaps
import Langlands.Representation.Archimedean.RealExponentDeformation
import Langlands.Representation.Archimedean.RealInjectiveIntertwinerStages
import Langlands.Representation.Archimedean.RealLargeLanglandsQuotientReduction

/-!
# Principal-series presentations of real standard modules with discrete-series blocks

For a list `Ds` of induction blocks of nonzero weight and a list `M` of blocks, this module
constructs a surjective `(𝔤, K)`-intertwiner from the principal series of
`x(D₁), …, x(D_r), M, y(D_r), …, y(D₁)` onto the standard module of `M, D_r, …, D₁`, where
`x(D) = |·|^{t - ℓ/2}` and `y(D) = sgn^{ℓ+1} |·|^{t + ℓ/2}` for `D` of weight `±ℓ` and
exponent `t`. It is a composite of the Library tail maps and of unlinked swaps.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

set_option backward.isDefEq.respectTransparency false

/-! ## Symmetry of linkage -/

theorem MoeglinDatum.IsLinked.symm {a b : MoeglinDatum} (h : a.IsLinked b) : b.IsLinked a := by
  cases a with
  | character ε s =>
    cases b with
    | character ε' s' =>
      obtain ⟨k, hk, hs, ho⟩ := h
      refine ⟨-k, neg_ne_zero.mpr hk, ?_, ?_⟩
      · push_cast
        rw [← hs]
        ring
      · have : -k + (ε'.val : ℤ) + (ε.val : ℤ) = (k + ε.val + ε'.val) - 2 * k := by ring
        rw [this]
        exact ho.sub_even (even_two_mul k)
    | discrete p s' =>
      obtain ⟨k, hk, h⟩ := h
      exact ⟨k, hk, h⟩
  | discrete p s =>
    cases b with
    | character ε' s' =>
      obtain ⟨k, hk, h⟩ := h
      exact ⟨k, hk, h⟩
    | discrete p' s' =>
      obtain ⟨k, hk, h⟩ := h
      refine ⟨k, hk, ?_⟩
      have e : ((p' : ℤ) - p).natAbs = ((p : ℤ) - p').natAbs := by omega
      rw [e]
      exact h.symm

theorem AreRealBlocksUnlinked.symm {x y : RealBlock} (h : AreRealBlocksUnlinked x y) :
    AreRealBlocksUnlinked y x :=
  fun a ha b hb hab => h b hb a ha hab.symm

namespace RealDiscretePresentation

variable {n : ℕ}

/-- The `O(n)`-finite functions of the real standard module of `ds`. -/
abbrev KF (n : ℕ) (ds : List RealBlock) :=
  kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)

/-- A `(𝔤, K)`-intertwiner between the `O(n)`-finite functions of two real standard modules. -/
abbrev IsGKMap (n : ℕ) (ds es : List RealBlock) (q : KF n ds →ₗ[ℂ] KF n es) : Prop :=
  IsRealStandardIntertwiner n (realStandardRep n es) (realStandardLie n es) ds q

/-- There is a surjective `(𝔤, K)`-intertwiner from the standard module of `ds` onto that of
`es`. -/
def HasGKSurjection (n : ℕ) (ds es : List RealBlock) : Prop :=
  ∃ q : KF n ds →ₗ[ℂ] KF n es, Function.Surjective q ∧ IsGKMap n ds es q

theorem HasGKSurjection.refl (ds : List RealBlock) : HasGKSurjection n ds ds :=
  ⟨LinearMap.id, Function.surjective_id, isRealStandardIntertwiner_id n ds⟩

theorem HasGKSurjection.of_eq {ds es : List RealBlock} (h : ds = es) : HasGKSurjection n ds es :=
  h ▸ HasGKSurjection.refl ds

theorem HasGKSurjection.trans {ds es fs : List RealBlock} (h₁ : HasGKSurjection n ds es)
    (h₂ : HasGKSurjection n es fs) : HasGKSurjection n ds fs := by
  obtain ⟨q₁, hs₁, hi₁⟩ := h₁
  obtain ⟨q₂, hs₂, hi₂⟩ := h₂
  exact ⟨q₂ ∘ₗ q₁, hs₂.comp hs₁, hi₁.comp_standard hi₂⟩

/-- The inverse of a bijective `(𝔤, K)`-intertwiner is a `(𝔤, K)`-intertwiner. -/
theorem isGKMap_symm {ds es : List RealBlock} {q : KF n ds →ₗ[ℂ] KF n es}
    (hq : IsGKMap n ds es q) (hb : Function.Bijective q) :
    IsGKMap n es ds (LinearEquiv.ofBijective q hb).symm.toLinearMap := by
  unfold IsGKMap at hq ⊢
  rw [InductionStages.isRealStandardIntertwiner_iff] at hq ⊢
  set e := LinearEquiv.ofBijective q hb
  have he : ∀ f, q (e.symm f) = f := fun f => e.apply_symm_apply f
  refine ⟨fun k f => ?_, fun X f => ?_⟩
  · apply hb.1
    simp only [LinearEquiv.coe_coe]
    rw [he, hq.1, he]
  · apply hb.1
    simp only [LinearEquiv.coe_coe]
    rw [he, hq.2, he]

theorem HasGKSurjection.of_bijective_symm {ds es : List RealBlock} {q : KF n ds →ₗ[ℂ] KF n es}
    (hq : IsGKMap n ds es q) (hb : Function.Bijective q) : HasGKSurjection n es ds :=
  ⟨_, (LinearEquiv.ofBijective q hb).symm.surjective, isGKMap_symm hq hb⟩

/-! ## Swaps of unlinked blocks -/

theorem realRank_swap_eq {pre post : List RealBlock} {x y : RealBlock}
    (h : realRank (pre ++ x :: y :: post) = n) : realRank (pre ++ y :: x :: post) = n := by
  rw [← h, RealSwapSurjective.realRank_swap, RealSwapSurjective.realRank_swap]
  omega

/-- The swap intertwiner of two unlinked blocks, the first of larger or equal real exponent, is
bijective. -/
theorem exists_bijective_swap {pre post : List RealBlock} {x y : RealBlock}
    (hn : realRank (pre ++ x :: y :: post) = n) (hle : realBlockExponent y ≤ realBlockExponent x)
    (hu : AreRealBlocksUnlinked x y) :
    ∃ q : KF n (pre ++ x :: y :: post) →ₗ[ℂ] KF n (pre ++ y :: x :: post),
      Function.Bijective q ∧ IsGKMap n _ _ q := by
  obtain ⟨T, hTi, hT⟩ := realUnlinkedSwap n pre post x y hn hle hu
  exact ⟨T, ⟨hTi, realSwapInjectiveIntertwinerSurjective n pre post x y T hn hTi hT⟩, hT⟩

/-- Two unlinked adjacent blocks can be exchanged, in either order of their real exponents. -/
theorem hasGKSurjection_swap {pre post : List RealBlock} {x y : RealBlock}
    (hn : realRank (pre ++ x :: y :: post) = n) (hu : AreRealBlocksUnlinked x y) :
    HasGKSurjection n (pre ++ x :: y :: post) (pre ++ y :: x :: post) := by
  rcases le_total (realBlockExponent y) (realBlockExponent x) with hle | hle
  · obtain ⟨q, hb, hq⟩ := exists_bijective_swap hn hle hu
    exact ⟨q, hb.2, hq⟩
  · obtain ⟨q, hb, hq⟩ := exists_bijective_swap (realRank_swap_eq hn) hle hu.symm
    exact HasGKSurjection.of_bijective_symm hq hb

/-- A block unlinked with every block of `zs` moves past `zs`. -/
theorem hasGKSurjection_move (x : RealBlock) :
    ∀ (zs pre post : List RealBlock), realRank (pre ++ x :: (zs ++ post)) = n →
      (∀ z ∈ zs, AreRealBlocksUnlinked x z) →
        HasGKSurjection n (pre ++ x :: (zs ++ post)) (pre ++ (zs ++ x :: post))
  | [], pre, post, _, _ => HasGKSurjection.of_eq (by simp)
  | z :: zs, pre, post, hn, hu => by
    have h₁ : HasGKSurjection n (pre ++ x :: z :: (zs ++ post))
        (pre ++ z :: x :: (zs ++ post)) :=
      hasGKSurjection_swap hn (hu z List.mem_cons_self)
    have e₁ : pre ++ z :: x :: (zs ++ post) = (pre ++ [z]) ++ x :: (zs ++ post) := by simp
    have hn' : realRank ((pre ++ [z]) ++ x :: (zs ++ post)) = n := by
      rw [← e₁]
      exact realRank_swap_eq hn
    have h₂ := hasGKSurjection_move x zs (pre ++ [z]) post hn'
      fun w hw => hu w (List.mem_cons_of_mem z hw)
    have e₂ : (pre ++ [z]) ++ (zs ++ x :: post) = pre ++ (z :: zs ++ x :: post) := by simp
    rw [e₁] at h₁
    rw [e₂] at h₂
    exact h₁.trans h₂

/-! ## The tail maps -/

/-- The sign `ℓ + 1 mod 2` of the second character of an induction block of weight `±ℓ`. -/
def ySign (d : ComplexCharacterData) : Fin 2 :=
  ⟨(d.weight.natAbs + 1) % 2, Nat.mod_lt _ (by norm_num)⟩

/-- The character `|·|^{t - ℓ/2}` of an induction block of weight `±ℓ` and exponent `t`. -/
def xBlock (d : ComplexCharacterData) : RealBlock :=
  .character (RealInducedCharacter.cb d 0)

/-- The character `sgn^{ℓ+1} |·|^{t + ℓ/2}` of an induction block of weight `±ℓ` and
exponent `t`. -/
def yBlock (d : ComplexCharacterData) : RealBlock :=
  .character (RealInducedCharacter.ca d (ySign d))

theorem realRank_xBlock_yBlock (d : ComplexCharacterData) :
    realRank [xBlock d, yBlock d] = realRank [RealBlock.induced d] := rfl

/-- The tail map of the block `d`: the principal series of `[x(d), y(d)]` maps onto the
induction block `d` when its weight is nonzero. -/
theorem hasGKSurjection_tail {pre post : List RealBlock} {d : ComplexCharacterData}
    (hn : realRank (pre ++ [RealBlock.induced d] ++ post) = n) (hl : 0 < d.weight.natAbs) :
    HasGKSurjection n (pre ++ [xBlock d, yBlock d] ++ post) (pre ++ [RealBlock.induced d] ++ post) := by
  have hs : ((ySign d).val + (0 : Fin 2).val) % 2 = (d.weight.natAbs + 1) % 2 := by
    simp [ySign]
  exact ⟨_, RealInducedCharacter.tail_surjective (sa := ySign d) (sb := 0) hn hl hs,
    RealExponentDeformation.isRealStandardIntertwiner_of_modulo_bot
      (RealInducedCharacter.modulo_tail (sa := ySign d) (sb := 0) hn hl hs)⟩

/-! ## The presentation -/

/-- The principal-series list `x(D₁), …, x(D_r), M, y(D_r), …, y(D₁)`. -/
def sourceList (Ds : List ComplexCharacterData) (M : List RealBlock) : List RealBlock :=
  Ds.map xBlock ++ M ++ Ds.reverse.map yBlock

/-- The standard-module list `M, D_r, …, D₁`. -/
def targetList (Ds : List ComplexCharacterData) (M : List RealBlock) : List RealBlock :=
  M ++ Ds.reverse.map RealBlock.induced

theorem realRank_sourceList (Ds : List ComplexCharacterData) (M : List RealBlock) :
    realRank (sourceList Ds M) = realRank (targetList Ds M) := by
  induction Ds with
  | nil => simp [sourceList, targetList]
  | cons d Ds ih =>
    simp only [sourceList, targetList, List.map_cons, List.reverse_cons, List.map_append,
      List.map_cons, List.map_nil] at ih ⊢
    simp only [realRank_append, realRank_cons, realRank_nil] at ih ⊢
    simp only [xBlock, yBlock, RealBlock.rank]
    omega

/-- **Presentation.** If every `x(D)` is unlinked with every block of `M` and with every block
`D'` after `D`, the principal series of `sourceList Ds M` maps onto the standard module of
`targetList Ds M`, inside arbitrary surrounding lists. -/
theorem hasGKSurjection_chain (M : List RealBlock) :
    ∀ (Ds : List ComplexCharacterData) (pre post : List RealBlock),
      realRank (pre ++ sourceList Ds M ++ post) = n →
      (∀ d ∈ Ds, 0 < d.weight.natAbs) →
      (∀ d ∈ Ds, ∀ z ∈ M, AreRealBlocksUnlinked (xBlock d) z) →
      Ds.Pairwise (fun d e => AreRealBlocksUnlinked (xBlock d) (RealBlock.induced e)) →
        HasGKSurjection n (pre ++ sourceList Ds M ++ post) (pre ++ targetList Ds M ++ post)
  | [], pre, post, _, _, _, _ => HasGKSurjection.of_eq (by simp [sourceList, targetList])
  | d :: Ds, pre, post, hn, hl, hM, hP => by
    have hP' := List.pairwise_cons.mp hP
    -- the inductive step inside `pre ++ [x(d)]` and `[y(d)] ++ post`
    have e₀ : pre ++ sourceList (d :: Ds) M ++ post =
        (pre ++ [xBlock d]) ++ sourceList Ds M ++ ([yBlock d] ++ post) := by
      simp [sourceList]
    have h₁ := hasGKSurjection_chain M Ds (pre ++ [xBlock d]) ([yBlock d] ++ post)
      (e₀ ▸ hn) (fun e he => hl e (List.mem_cons_of_mem d he))
      (fun e he => hM e (List.mem_cons_of_mem d he)) hP'.2
    rw [← e₀] at h₁
    -- move `x(d)` past the target of the inductive step
    have e₁ : (pre ++ [xBlock d]) ++ targetList Ds M ++ ([yBlock d] ++ post) =
        pre ++ xBlock d :: (targetList Ds M ++ yBlock d :: post) := by
      simp
    rw [e₁] at h₁
    have hn₁ : realRank (pre ++ xBlock d :: (targetList Ds M ++ yBlock d :: post)) = n := by
      rw [← e₁, ← hn, e₀]
      simp only [realRank_append, realRank_sourceList]
    have h₂ := hasGKSurjection_move (xBlock d) (targetList Ds M) pre (yBlock d :: post) hn₁
      (by
        intro z hz
        rcases List.mem_append.mp hz with hz | hz
        · exact hM d List.mem_cons_self z hz
        · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hz
          exact hP'.1 e (List.mem_reverse.mp he))
    -- the tail map of `d`
    have e₂ : pre ++ (targetList Ds M ++ xBlock d :: yBlock d :: post) =
        (pre ++ targetList Ds M) ++ [xBlock d, yBlock d] ++ post := by
      simp
    rw [e₂] at h₂
    have e₃ : pre ++ targetList (d :: Ds) M ++ post =
        (pre ++ targetList Ds M) ++ [RealBlock.induced d] ++ post := by
      simp [targetList]
    have hn₃ : realRank ((pre ++ targetList Ds M) ++ [RealBlock.induced d] ++ post) = n := by
      rw [← hn, e₀]
      simp only [realRank_append, realRank_sourceList, realRank_cons, realRank_nil]
      simp only [xBlock, yBlock, RealBlock.rank]
      omega
    have h₃ := hasGKSurjection_tail hn₃ (hl d List.mem_cons_self)
    rw [e₃]
    exact h₁.trans (h₂.trans h₃)

end RealDiscretePresentation

end Langlands.Archimedean
