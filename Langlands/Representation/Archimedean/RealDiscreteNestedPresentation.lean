import Langlands.Representation.Archimedean.RealInducedCharacterMaps
import Langlands.Representation.Archimedean.RealExponentDeformation
import Langlands.Representation.Archimedean.RealLinkedLanglandsQuotientNotLargeProof
import Langlands.Representation.Archimedean.RealSplitFrobenius

/-!
# A nested principal-series presentation for tied discrete blocks

Put the low endpoints in increasing order of the absolute block weights, and
the high endpoints in reverse order. Contract the largest low/high pair and
move the resulting block past the remaining highs. Iterating gives a
surjection. Splitting the resulting blocks individually gives an injection
into a principal series with the same multiset of characters.
-/

noncomputable section

open scoped TensorProduct

set_option autoImplicit false

namespace Langlands.Archimedean.RealDiscreteNestedPresentation

open Langlands.LocalFactor.Archimedean
open RealCharacterPairReducible RealInducedCharacter RealStandardFiltration

attribute [local instance 100] LieRing.ofAssociativeRing

set_option backward.isDefEq.respectTransparency false

/-- Sign of the low endpoint, chosen so that its signed exponent class depends only on the
weight parity and the block exponent. -/
def lowSign (d : ComplexCharacterData) : Fin 2 :=
  ⟨d.weight.natAbs / 2 % 2, Nat.mod_lt _ (by decide)⟩

/-- Sign of the high endpoint, chosen to satisfy the rank-two tail parity condition. -/
def highSign (d : ComplexCharacterData) : Fin 2 :=
  ⟨(d.weight.natAbs / 2 + d.weight.natAbs + 1) % 2, Nat.mod_lt _ (by decide)⟩

theorem endpoint_signs (d : ComplexCharacterData) :
    ((highSign d).val + (lowSign d).val) % 2 = (d.weight.natAbs + 1) % 2 := by
  simp only [highSign, lowSign]
  omega

/-- Low endpoint of the block. -/
def low (d : ComplexCharacterData) : RealCharacterData := cb d (lowSign d)

/-- High endpoint of the block. -/
def high (d : ComplexCharacterData) : RealCharacterData := ca d (highSign d)

/-- Ascending pair at the middle of the donor list. -/
def nestedChars (ds : List ComplexCharacterData) : List RealCharacterData :=
  ds.reverse.map low ++ ds.map high

/-- Adjacent high/low pairs in block order. -/
def splitChars (ds : List ComplexCharacterData) : List RealCharacterData :=
  ds.flatMap fun d => [high d, low d]

theorem nestedChars_perm_splitChars (ds : List ComplexCharacterData) :
    (nestedChars ds).Perm (splitChars ds.reverse) := by
  induction ds with
  | nil => exact List.Perm.nil
  | cons d ds ih =>
    simp only [nestedChars, splitChars, List.reverse_cons, List.map_append, List.map_cons,
      List.map_nil, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    change ((ds.reverse.map low ++ [low d]) ++ high d :: ds.map high).Perm
      (splitChars ds.reverse ++ [high d, low d])
    have h : ((ds.reverse.map low ++ [low d]) ++ high d :: ds.map high).Perm
        (nestedChars ds ++ [high d, low d]) := by
      simpa only [nestedChars, List.append_assoc, List.cons_append, List.nil_append] using
        (List.perm_append_comm (l₁ := [low d, high d]) (l₂ := ds.map high)
          |>.trans ((List.Perm.swap (high d) (low d) []).append_left (ds.map high)))
          |>.append_left (ds.reverse.map low)
    exact h.trans (ih.append_right _)

private theorem high_unlinked_of_le {d e : ComplexCharacterData}
    (hle : d.weight.natAbs ≤ e.weight.natAbs) (hre : d.exponent.re = e.exponent.re)
    (hnz : e.weight ≠ 0) :
    AreRealBlocksUnlinked (.character (high d)) (.induced e) := by
  intro a ha b hb
  simp only [realBlockMoeglinData, hnz, ↓reduceIte, List.mem_singleton] at ha hb
  subst a
  subst b
  rintro ⟨k, hk, heq | heq⟩
  all_goals
    have hle' : (d.weight.natAbs : ℝ) ≤ (e.weight.natAbs : ℝ) := by exact_mod_cast hle
    have hk' : (0 : ℝ) < k := Nat.cast_pos.mpr hk
    have heq' := congrArg Complex.re heq
    simp only [high, ca_exponent, aExp, Complex.sub_re, Complex.add_re, Complex.div_ofNat_re,
      Complex.natCast_re, hre] at heq'
    linarith

private theorem exact_inverse {n : ℕ} {xs ys : List RealBlock}
    {T : KF n xs →ₗ[ℂ] KF n ys}
    (hT : IsRealStandardIntertwiner n (realStandardRep n ys) (realStandardLie n ys) xs T)
    (hb : Function.Bijective T) : RealSurjectiveIntertwinerExists n ys xs := by
  let e := LinearEquiv.ofBijective T hb
  have hsection (f : KF n ys) : T (e.symm f) = f := e.apply_symm_apply f
  apply Exists.intro e.symm.toLinearMap
  refine ⟨e.symm.surjective, RealSplitFrobenius.Commutes.isRealStandardIntertwiner
    ⟨fun k f => ?_, fun X f => ?_⟩⟩
  · apply hb.1
    simp only [LinearEquiv.coe_coe]
    rw [hsection, hT.map_realStandardRep, hsection]
  · apply hb.1
    simp only [LinearEquiv.coe_coe]
    rw [hsection, hT.map_realStandardLie, hsection]

private theorem moveRight {n : ℕ} (z : RealBlock) :
    ∀ (mid pre post : List RealBlock), realRank (pre ++ z :: (mid ++ post)) = n →
      (∀ w ∈ mid, realBlockExponent z ≤ realBlockExponent w ∧ AreRealBlocksUnlinked w z) →
      RealSurjectiveIntertwinerExists n (pre ++ z :: (mid ++ post)) (pre ++ mid ++ z :: post)
  | [], pre, post, _, _ => by simpa using RealSurjectiveIntertwinerExists.refl n (pre ++ z :: post)
  | w :: mid, pre, post, hn, hmid => by
    have hRank : realRank (pre ++ w :: z :: (mid ++ post)) = n := by
      rw [← hn]
      exact realRank_perm ((List.Perm.swap z w (mid ++ post)).append_left pre)
    obtain ⟨T, hTi, hT⟩ := realUnlinkedSwap n pre (mid ++ post) w z hRank
      (hmid w List.mem_cons_self).1 (hmid w List.mem_cons_self).2
    have hswap := exact_inverse hT
      ⟨hTi, realSwapInjectiveIntertwinerSurjective n pre (mid ++ post) w z T hRank hTi hT⟩
    have hRank' : realRank ((pre ++ [w]) ++ z :: (mid ++ post)) = n := by
      simpa using hRank
    have hrest := moveRight z mid (pre ++ [w]) post hRank'
      fun x hx => hmid x (List.mem_cons_of_mem w hx)
    have hrest' : RealSurjectiveIntertwinerExists n (pre ++ w :: z :: (mid ++ post))
        (pre ++ (w :: mid) ++ z :: post) := by simpa using hrest
    exact hswap.trans hrest'

/-- The nested principal series surjects onto the reversed list of tied induction blocks. -/
theorem nested_surjection {n : ℕ} {r : ℝ} :
    ∀ (ds : List ComplexCharacterData) (pre post : List RealBlock),
      realRank (pre ++ (nestedChars ds).map RealBlock.character ++ post) = n →
      (∀ d ∈ ds, d.weight ≠ 0) → (∀ d ∈ ds, d.exponent.re = r) →
      ds.Pairwise (fun d e => e.weight.natAbs ≤ d.weight.natAbs) →
      RealSurjectiveIntertwinerExists n (pre ++ (nestedChars ds).map RealBlock.character ++ post)
        (pre ++ ds.reverse.map RealBlock.induced ++ post)
  | [], pre, post, _, _, _, _ => by
    simpa [nestedChars] using RealSurjectiveIntertwinerExists.refl n (pre ++ post)
  | d :: ds, pre, post, hn, hw, ht, hord => by
    let p := pre ++ (ds.reverse.map low).map RealBlock.character
    let hs := (ds.map high).map RealBlock.character
    have hshape : pre ++ (nestedChars (d :: ds)).map RealBlock.character ++ post =
        p ++ [RealBlock.character (low d), RealBlock.character (high d)] ++ (hs ++ post) := by
      simp [p, hs, nestedChars, List.map_append, List.append_assoc]
    have hn' : realRank (p ++ [RealBlock.induced d] ++ (hs ++ post)) = n := by
      rw [← hn, hshape]
      exact realRank_mid_eq p (hs ++ post) rfl
    have htail : RealSurjectiveIntertwinerExists n
        (p ++ [RealBlock.character (low d), RealBlock.character (high d)] ++ (hs ++ post))
        (p ++ [RealBlock.induced d] ++ (hs ++ post)) :=
      ⟨_, tail_surjective hn' (Int.natAbs_pos.mpr (hw d List.mem_cons_self)) (endpoint_signs d),
        RealExponentDeformation.isRealStandardIntertwiner_of_modulo_bot
          (modulo_tail hn' (Int.natAbs_pos.mpr (hw d List.mem_cons_self)) (endpoint_signs d))⟩
    have hmove := moveRight (RealBlock.induced d) hs p post (by simpa using hn') (by
      intro w hw'
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hw'
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hc
      have hre : e.exponent.re = d.exponent.re := by
        rw [ht e (List.mem_cons_of_mem d he), ht d List.mem_cons_self]
      refine ⟨?_, high_unlinked_of_le ((List.pairwise_cons.mp hord).1 e he) hre
        (hw d List.mem_cons_self)⟩
      change d.exponent.re ≤ (aExp e).re
      rw [aExp, Complex.add_re, hre, Complex.div_ofNat_re, Complex.natCast_re]
      have hweight : (0 : ℝ) ≤ e.weight.natAbs := Nat.cast_nonneg _
      linarith)
    have hmove' : RealSurjectiveIntertwinerExists n
        (p ++ [RealBlock.induced d] ++ (hs ++ post))
        (pre ++ (nestedChars ds).map RealBlock.character ++ (RealBlock.induced d :: post)) := by
      simpa [p, hs, nestedChars, List.map_append, List.append_assoc] using hmove
    have hn'' : realRank
        (pre ++ (nestedChars ds).map RealBlock.character ++ (RealBlock.induced d :: post)) = n := by
      rw [← hn']
      simp only [p, hs, nestedChars, List.map_append, realRank_append, realRank_cons, realRank_nil]
      omega
    have hrec := nested_surjection ds pre (RealBlock.induced d :: post) hn''
      (fun e he => hw e (List.mem_cons_of_mem d he)) (fun e he => ht e (List.mem_cons_of_mem d he))
      (List.pairwise_cons.mp hord).2
    simpa only [hshape, List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      List.append_assoc, List.cons_append, List.nil_append] using htail.trans (hmove'.trans hrec)

end Langlands.Archimedean.RealDiscreteNestedPresentation
