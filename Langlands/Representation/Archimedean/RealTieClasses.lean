import Langlands.Representation.Archimedean.RealLeviSlices
import Langlands.Representation.Archimedean.RealInducedStandardBound
import Langlands.Representation.Archimedean.RealTemperedIrreducibleStatement
import Langlands.Representation.Archimedean.RealGenericParameterReduction

/-!
# Tie classes of a Langlands-ordered list of real blocks

A Langlands-ordered list `ds` of real blocks (real parts of the block exponents weakly
decreasing) is cut into its **tie classes**: maximal runs of consecutive blocks whose exponents
have the same real part. With `dss i` the `i`-th class (`i < c`), `ds = dss 0 ++ ⋯ ++ dss (c-1)`
(`flat dss`). The real parts of the exponents are constant on each class and strictly decrease
from one class to the next (`exists_tieClasses`).

For the standard parabolic subgroup `Q` with diagonal blocks of sizes `sz_i = realRank (dss i)`
this gives the two exponent conditions of the limit along `Q` (`RealLeviLimit`): the position
block exponents of `flat dss` weakly decrease (`anti_of_tieClasses`) and strictly decrease
across the blocks of `Q` (`strict_of_tieClasses`). The twisted class lists `cl dss i` have
constant real exponent, so their standard modules are irreducible given
`RealTemperedStandardIrreducibleStatement` (`irreducible_cl`). `exists_tieData` packages
everything.
-/

noncomputable section

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

attribute [local instance 100] LieRing.ofAssociativeRing

namespace RealTieClasses

open RealLeviChart RealLeviSlices RealInducedStandardBound

/-! ## Position block exponents -/

/-- Every position block exponent is the real exponent of a block of the list. -/
theorem exists_mem_realPositionBlockExponent :
    ∀ (ds : List RealBlock) (p : ℕ), p < realRank ds →
      ∃ x ∈ ds, realPositionBlockExponent ds p = realBlockExponent x
  | [], p, hp => by simp [realRank] at hp
  | .character _ :: _, 0, _ => ⟨_, List.mem_cons_self .., rfl⟩
  | .character _ :: ds, p + 1, hp => by
      have hp' : p < realRank ds := by
        rw [realRank_cons] at hp
        simp only [RealBlock.rank] at hp
        omega
      obtain ⟨x, hx, e⟩ := exists_mem_realPositionBlockExponent ds p hp'
      exact ⟨x, List.mem_cons_of_mem _ hx, e⟩
  | .induced _ :: _, 0, _ => ⟨_, List.mem_cons_self .., rfl⟩
  | .induced _ :: _, 1, _ => ⟨_, List.mem_cons_self .., rfl⟩
  | .induced _ :: ds, p + 2, hp => by
      have hp' : p < realRank ds := by
        rw [realRank_cons] at hp
        simp only [RealBlock.rank] at hp
        omega
      obtain ⟨x, hx, e⟩ := exists_mem_realPositionBlockExponent ds p hp'
      exact ⟨x, List.mem_cons_of_mem _ hx, e⟩

theorem realPositionBlockExponent_append_left :
    ∀ (A B : List RealBlock) (p : ℕ), p < realRank A →
      realPositionBlockExponent (A ++ B) p = realPositionBlockExponent A p
  | [], _, p, hp => by simp [realRank_nil] at hp
  | .character _ :: _, _, 0, _ => rfl
  | .character _ :: A, B, p + 1, hp => by
      simp only [List.cons_append, realPositionBlockExponent]
      refine realPositionBlockExponent_append_left A B p ?_
      rw [realRank_cons] at hp
      simp only [RealBlock.rank] at hp
      omega
  | .induced _ :: _, _, 0, _ => rfl
  | .induced _ :: _, _, 1, _ => rfl
  | .induced _ :: A, B, p + 2, hp => by
      simp only [List.cons_append, realPositionBlockExponent]
      refine realPositionBlockExponent_append_left A B p ?_
      rw [realRank_cons] at hp
      simp only [RealBlock.rank] at hp
      omega

theorem realPositionBlockExponent_append_right :
    ∀ (A B : List RealBlock) (p : ℕ),
      realPositionBlockExponent (A ++ B) (realRank A + p) = realPositionBlockExponent B p
  | [], _, p => by simp [realRank_nil]
  | .character d :: A, B, p => by
      have h : realRank (.character d :: A) + p = (realRank A + p) + 1 := by
        rw [realRank_cons]
        simp only [RealBlock.rank]
        omega
      rw [List.cons_append, h]
      exact realPositionBlockExponent_append_right A B p
  | .induced d :: A, B, p => by
      have h : realRank (.induced d :: A) + p = (realRank A + p) + 2 := by
        rw [realRank_cons]
        simp only [RealBlock.rank]
        omega
      rw [List.cons_append, h]
      exact realPositionBlockExponent_append_right A B p

theorem realPositionBlockExponent_flat : ∀ {c : ℕ} (dss : Fin c → List RealBlock) (i : Fin c)
    (a : ℕ), a < sz dss i →
      realPositionBlockExponent (flat dss) (start (sz dss) i + a) =
        realPositionBlockExponent (dss i) a
  | 0, _, i, _, _ => i.elim0
  | c + 1, dss, i, a, ha => by
      rw [flat_succ]
      induction i using Fin.cases with
      | zero =>
          rw [Fin.val_zero, start_zero', zero_add]
          exact realPositionBlockExponent_append_left _ _ a ha
      | succ i =>
          rw [Fin.val_succ, start_succ', add_assoc]
          have e : sz dss 0 = realRank (dss 0) := rfl
          rw [e, realPositionBlockExponent_append_right]
          exact realPositionBlockExponent_flat (fun j => dss j.succ) i a ha

/-- The position block exponent of `flat dss` at a position of the block `i` of `Q` is the real
exponent of a block of the class `dss i`. -/
theorem exists_mem_flat {c : ℕ} (dss : Fin c → List RealBlock) (p : Fin (∑ i, sz dss i)) :
    ∃ x ∈ dss (cls (sz dss) p),
      realPositionBlockExponent (flat dss) p = realBlockExponent x := by
  obtain ⟨a, ha⟩ := pos_cls (sz dss) p
  have hp : (p : ℕ) = start (sz dss) (cls (sz dss) p) + a := by rw [← val_pos, ha]
  rw [hp, realPositionBlockExponent_flat dss _ a a.2]
  exact exists_mem_realPositionBlockExponent _ a a.2

theorem mem_flat {c : ℕ} {dss : Fin c → List RealBlock} {i : Fin c} {x : RealBlock}
    (hx : x ∈ dss i) : x ∈ flat dss :=
  List.mem_flatten.mpr ⟨dss i, by simp, hx⟩

/-! ## Tie classes -/

/-- **Tie classes.** A Langlands-ordered list of real blocks is the concatenation of nonempty
classes on which the real exponent is constant and which have strictly decreasing real
exponents. -/
theorem exists_tieClasses : ∀ ds : List RealBlock, IsRealLanglandsOrdered ds →
    ∃ (c : ℕ) (dss : Fin c → List RealBlock), flat dss = ds ∧ (∀ i, dss i ≠ []) ∧
      (∀ i, ∀ x ∈ dss i, ∀ y ∈ dss i, realBlockExponent x = realBlockExponent y) ∧
      (∀ i j : Fin c, i < j → ∀ x ∈ dss i, ∀ y ∈ dss j,
        realBlockExponent y < realBlockExponent x)
  | [], _ => ⟨0, Fin.elim0, rfl, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | b :: ds, hord => by
      obtain ⟨hb, hds⟩ := List.pairwise_cons.mp hord
      obtain ⟨c, dss, hflat, hne, heq, hlt⟩ := exists_tieClasses ds hds
      cases c with
      | zero =>
          have hnil : ds = [] := by rw [← hflat]; rfl
          subst hnil
          refine ⟨1, fun _ => [b], by simp [flat], fun _ => List.cons_ne_nil _ _, ?_, ?_⟩
          · intro _ x hx y hy
            rw [List.mem_singleton] at hx hy
            rw [hx, hy]
          · intro i j hij
            exact absurd hij (by omega)
      | succ c =>
          obtain ⟨x0, hx0⟩ := List.exists_mem_of_ne_nil _ (hne 0)
          have hx0b : realBlockExponent x0 ≤ realBlockExponent b :=
            hb x0 (hflat ▸ mem_flat hx0)
          by_cases htie : ∀ x ∈ dss 0, realBlockExponent x = realBlockExponent b
          · -- `b` joins the first class
            have hcls : ∀ x ∈ b :: dss 0, realBlockExponent x = realBlockExponent b := by
              intro x hx
              rcases List.mem_cons.mp hx with rfl | hx
              · rfl
              · exact htie x hx
            refine ⟨c + 1, Fin.cons (b :: dss 0) (fun i => dss i.succ), ?_, ?_, ?_, ?_⟩
            · rw [flat_succ]
              simp only [Fin.cons_zero, Fin.cons_succ, List.cons_append]
              rw [← hflat, flat_succ]
            · intro i
              induction i using Fin.cases with
              | zero => exact List.cons_ne_nil _ _
              | succ i => simpa using hne i.succ
            · intro i
              induction i using Fin.cases with
              | zero =>
                  intro x hx y hy
                  simp only [Fin.cons_zero] at hx hy
                  rw [hcls x hx, hcls y hy]
              | succ i =>
                  simpa using heq i.succ
            · intro i j hij
              induction j using Fin.cases with
              | zero => exact absurd hij (Fin.not_lt_zero _)
              | succ j =>
                  induction i using Fin.cases with
                  | zero =>
                      intro x hx y hy
                      simp only [Fin.cons_zero, Fin.cons_succ] at hx hy
                      rw [hcls x hx, ← htie x0 hx0]
                      exact hlt 0 j.succ (Fin.succ_pos _) x0 hx0 y hy
                  | succ i =>
                      intro x hx y hy
                      simp only [Fin.cons_succ] at hx hy
                      exact hlt i.succ j.succ hij x hx y hy
          · -- `b` starts a new class
            push Not at htie
            obtain ⟨x1, hx1, hx1b⟩ := htie
            have hlt0 : realBlockExponent x0 < realBlockExponent b := by
              rw [← heq 0 x1 hx1 x0 hx0]
              exact lt_of_le_of_ne (hb x1 (hflat ▸ mem_flat hx1)) hx1b
            refine ⟨c + 2, Fin.cons [b] dss, ?_, ?_, ?_, ?_⟩
            · rw [flat_succ]
              simp only [Fin.cons_zero, Fin.cons_succ, List.singleton_append]
              rw [← hflat]
            · intro i
              induction i using Fin.cases with
              | zero => exact List.cons_ne_nil _ _
              | succ i => simpa using hne i
            · intro i
              induction i using Fin.cases with
              | zero =>
                  intro x hx y hy
                  simp only [Fin.cons_zero, List.mem_singleton] at hx hy
                  rw [hx, hy]
              | succ i =>
                  simpa using heq i
            · intro i j hij
              induction j using Fin.cases with
              | zero => exact absurd hij (Fin.not_lt_zero _)
              | succ j =>
                  induction i using Fin.cases with
                  | zero =>
                      intro x hx y hy
                      simp only [Fin.cons_zero, Fin.cons_succ, List.mem_singleton] at hx hy
                      rw [hx]
                      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
                      · rw [heq 0 y hy x0 hx0]
                        exact hlt0
                      · exact (hlt 0 j'.succ (Fin.succ_pos _) x0 hx0 y hy).trans hlt0
                  | succ i =>
                      intro x hx y hy
                      simp only [Fin.cons_succ] at hx hy
                      exact hlt i j (Fin.succ_lt_succ_iff.mp hij) x hx y hy

/-! ## The exponent conditions along the tie classes -/

section Conditions

variable {c : ℕ} {dss : Fin c → List RealBlock}

/-- The position block exponents of `flat dss` weakly decrease. -/
theorem anti_of_tieClasses
    (heq : ∀ i, ∀ x ∈ dss i, ∀ y ∈ dss i, realBlockExponent x = realBlockExponent y)
    (hlt : ∀ i j : Fin c, i < j → ∀ x ∈ dss i, ∀ y ∈ dss j,
      realBlockExponent y < realBlockExponent x) :
    ∀ p q : Fin (∑ i, sz dss i), p ≤ q →
      realPositionBlockExponent (flat dss) q ≤ realPositionBlockExponent (flat dss) p := by
  intro p q hpq
  obtain ⟨x, hx, ex⟩ := exists_mem_flat dss p
  obtain ⟨y, hy, ey⟩ := exists_mem_flat dss q
  rw [ex, ey]
  rcases (cls_mono (sz dss) hpq).lt_or_eq with h | h
  · exact (hlt _ _ h x hx y hy).le
  · rw [h] at hx
    exact (heq _ y hy x hx).le

/-- The position block exponents of `flat dss` strictly decrease across the blocks of `Q`. -/
theorem strict_of_tieClasses
    (hlt : ∀ i j : Fin c, i < j → ∀ x ∈ dss i, ∀ y ∈ dss j,
      realBlockExponent y < realBlockExponent x) :
    ∀ p q : Fin (∑ i, sz dss i), cls (sz dss) p < cls (sz dss) q →
      realPositionBlockExponent (flat dss) q < realPositionBlockExponent (flat dss) p := by
  intro p q h
  obtain ⟨x, hx, ex⟩ := exists_mem_flat dss p
  obtain ⟨y, hy, ey⟩ := exists_mem_flat dss q
  rw [ex, ey]
  exact hlt _ _ h x hx y hy

/-- The twisted class standard modules are irreducible, given irreducibility of standard modules
with constant real exponent. -/
theorem irreducible_cl (htemp : RealTemperedStandardIrreducibleStatement)
    (heq : ∀ i, ∀ x ∈ dss i, ∀ y ∈ dss i, realBlockExponent x = realBlockExponent y)
    (i : Fin c) :
    IsIrreducibleGKModule (realStandardRep (sz dss i) (cl dss i))
      (realStandardLie (sz dss i) (cl dss i)) := by
  refine htemp _ _ (realRank_cl dss i) fun x hx y hy => ?_
  have hx2 : x ∈ List.map (twistBlock (shift dss i)) (dss i) := hx
  have hy2 : y ∈ List.map (twistBlock (shift dss i)) (dss i) := hy
  obtain ⟨x', hx', rfl⟩ := List.mem_map.mp hx2
  obtain ⟨y', hy', rfl⟩ := List.mem_map.mp hy2
  rw [realBlockExponent_twistBlock, realBlockExponent_twistBlock, heq i x' hx' y' hy']

end Conditions

/-- **Tie data.** Given `RealTemperedStandardIrreducibleStatement`, every Langlands-ordered list
`ds` of real blocks is `flat dss` for classes `dss` such that the position block exponents of
`flat dss` weakly decrease, strictly decrease across the blocks of `Q` (sizes `sz dss`), and
every twisted class standard module is irreducible. -/
theorem exists_tieData (htemp : RealTemperedStandardIrreducibleStatement) (ds : List RealBlock)
    (hord : IsRealLanglandsOrdered ds) :
    ∃ (c : ℕ) (dss : Fin c → List RealBlock), flat dss = ds ∧
      (∀ p q : Fin (∑ i, sz dss i), p ≤ q →
        realPositionBlockExponent (flat dss) q ≤ realPositionBlockExponent (flat dss) p) ∧
      (∀ p q : Fin (∑ i, sz dss i), cls (sz dss) p < cls (sz dss) q →
        realPositionBlockExponent (flat dss) q < realPositionBlockExponent (flat dss) p) ∧
      ∀ i, IsIrreducibleGKModule (realStandardRep (sz dss i) (cl dss i))
        (realStandardLie (sz dss i) (cl dss i)) := by
  obtain ⟨c, dss, hflat, -, heq, hlt⟩ := exists_tieClasses ds hord
  exact ⟨c, dss, hflat, anti_of_tieClasses heq hlt, strict_of_tieClasses hlt,
    irreducible_cl htemp heq⟩

end RealTieClasses

end Langlands.Archimedean
