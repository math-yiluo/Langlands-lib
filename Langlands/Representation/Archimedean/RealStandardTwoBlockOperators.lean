import Langlands.Representation.Archimedean.RealInducedCompactBlockProduct
import Langlands.Representation.Archimedean.RealInducedCompactMultiplier
import Langlands.Representation.Archimedean.RealStandardBlockLocalization
import Langlands.Representation.Archimedean.RealStandardReplacementInStages
import Langlands.Representation.Archimedean.RealLeviParabolicIntegration

/-! # Compact behavior of operators induced from two consecutive factors -/

noncomputable section

open scoped TensorProduct Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.InductionStages

open Langlands.LocalFactor.Archimedean
open RealLeviChart RealLeviSlices RealLeviBlockHaar RealLeviParabolicIntegration RealLeviProducts
open RealInducedBlockBound RealInducedTorusCore RealTemperedForm

attribute [local instance 100] LieRing.ofAssociativeRing

private abbrev G (n : ℕ) := Langlands.GeneralLinear n ℝ
private abbrev K (n : ℕ) := unitaryCompact ℝ n

section BlockOperator

variable {c : ℕ} (s : Fin c → ℕ)

local notation "N" => ∑ i, s i

private theorem blockEmbK_mem_compactLevi (i : Fin c) (h : start s i + s i ≤ N)
    (l : K (s i)) : (blockEmbK h l).val ∈ Kc (cls s) := by
  let κ : ∀ j, K (s j) := Pi.mulSingle i l
  have hκ : (fun j => (κ j).val) = Pi.mulSingle i l.val := by
    funext j
    by_cases hj : j = i
    · subst j
      simp only [κ, Pi.mulSingle_eq_same]
    · simp only [κ, Pi.mulSingle_eq_of_ne hj, Subgroup.coe_one]
  have him := bd_mem_Kc κ
  change blockDiagGL s (fun j => (κ j).val) ∈ Kc (cls s) at him
  rw [hκ, ← emb_eq, emb_eq_blockEmb s i h] at him
  rwa [coe_blockEmbK]

theorem ind_commutesWithBlockMultipliers (i : Fin c) {pre ds es post : List RealBlock}
    (h : start s i + s i ≤ N) (ha : realRank pre = start s i)
    (hd : realRank ds = s i) (he : realRank es = s i)
    (hn : realRank (pre ++ es ++ post) = N)
    (T : KFin (s i) ds →ₗ[ℂ] KFin (s i) es)
    (hT : ∀ k f, T (kRep (s i) ds k f) = kRep (s i) es k (T f)) :
    CommutesWithBlockMultipliers (cls s) (ind h ha he hd hn T hT) := by
  intro φ hφ F f hF
  refine realInducedCompactMultiplier h ha hd he hn T hT φ (fun l k => ?_) F f hF
  let l' : Kc (cls s) := ⟨(blockEmbK h l).val, blockEmbK_mem_compactLevi s i h l⟩
  exact hφ l' k

end BlockOperator

section Two

variable (s : Fin 2 → ℕ)

local notation "N" => ∑ i, s i

/-- A compact restriction given by a product of two consecutive factors. -/
def IsTwoBlockCompactProduct (F : G N → ℂ) (u : G (s 0) → ℂ) (v : G (s 1) → ℂ) : Prop :=
  ∀ κ : ∀ i, K (s i), F (bd κ) = u (κ 0).val * v (κ 1).val

/-- The compact action on both factors of every pure product. -/
def ActsOnTwoCompactFactors {ds es A B A' B' : List RealBlock}
    (T : KFin N ds →ₗ[ℂ] KFin N es)
    (L : KFin (s 0) A →ₗ[ℂ] KFin (s 0) A')
    (R : KFin (s 1) B →ₗ[ℂ] KFin (s 1) B') : Prop :=
  ∀ (F : KFin N ds) (u : KFin (s 0) A) (v : KFin (s 1) B),
    IsTwoBlockCompactProduct s F.val u.val v.val →
    IsTwoBlockCompactProduct s (T F).val (L u).val (R v).val

private theorem ind_left_product {pre ds es post : List RealBlock}
    (h : start s 0 + s 0 ≤ N) (ha : realRank pre = start s 0)
    (hd : realRank ds = s 0) (he : realRank es = s 0)
    (hn : realRank (pre ++ es ++ post) = N)
    (T : KFin (s 0) ds →ₗ[ℂ] KFin (s 0) es)
    (hT : ∀ k f, T (kRep (s 0) ds k f) = kRep (s 0) es k (T f))
    (F : KFin N (pre ++ ds ++ post)) (u : KFin (s 0) ds) (v : G (s 1) → ℂ)
    (hF : IsTwoBlockCompactProduct s F.val u.val v) :
    IsTwoBlockCompactProduct s (ind h ha he hd hn T hT F).val (T u).val v := by
  let f : ∀ j, G (s j) → ℂ := Fin.cons u.val (Fin.cons v fun j => j.elim0)
  have hf (κ : ∀ j, K (s j)) : F.val (bd κ) = ∏ j, f j (κ j).val := by
    rw [Fin.prod_univ_two]
    exact hF κ
  intro κ
  have e := realInducedCompactBlockProduct s 0 h ha hd he hn T hT F f u rfl hf κ
  have heq : Finset.univ \ ({0} : Finset (Fin 2)) = {1} := by decide
  rw [heq, Finset.prod_singleton] at e
  exact e

private theorem ind_right_product {pre ds es post : List RealBlock}
    (h : start s 1 + s 1 ≤ N) (ha : realRank pre = start s 1)
    (hd : realRank ds = s 1) (he : realRank es = s 1)
    (hn : realRank (pre ++ es ++ post) = N)
    (T : KFin (s 1) ds →ₗ[ℂ] KFin (s 1) es)
    (hT : ∀ k f, T (kRep (s 1) ds k f) = kRep (s 1) es k (T f))
    (F : KFin N (pre ++ ds ++ post)) (u : G (s 0) → ℂ) (v : KFin (s 1) ds)
    (hF : IsTwoBlockCompactProduct s F.val u v.val) :
    IsTwoBlockCompactProduct s (ind h ha he hd hn T hT F).val u (T v).val := by
  let f : ∀ j, G (s j) → ℂ := Fin.cons u (Fin.cons v.val fun j => j.elim0)
  have hf (κ : ∀ j, K (s j)) : F.val (bd κ) = ∏ j, f j (κ j).val := by
    rw [Fin.prod_univ_two]
    exact hF κ
  intro κ
  have e := realInducedCompactBlockProduct s 1 h ha hd he hn T hT F f v rfl hf κ
  have heq : Finset.univ \ ({1} : Finset (Fin 2)) = {0} := by decide
  rw [heq, Finset.prod_singleton, mul_comm] at e
  exact e

private theorem start_one : start s 1 = s 0 := by
  change start s (0 + 1) = s 0
  rw [start_succ', start_zero', add_zero]

private theorem left_le : start s 0 + s 0 ≤ N := by
  rw [start_zero', zero_add, Fin.sum_univ_two]
  omega

private theorem right_le : start s 1 + s 1 ≤ N := by
  rw [start_one, Fin.sum_univ_two]

private theorem rank_append {A B : List RealBlock}
    (hA : realRank A = s 0) (hB : realRank B = s 1) : realRank (A ++ B) = N := by
  rw [RealLeviSlices.realRank_append, hA, hB, Fin.sum_univ_two]

private theorem actsOnTwoCompactFactors_comp {ds es fs A B A' B' A'' B'' : List RealBlock}
    {T : KFin N ds →ₗ[ℂ] KFin N es} {U : KFin N es →ₗ[ℂ] KFin N fs}
    {L : KFin (s 0) A →ₗ[ℂ] KFin (s 0) A'}
    {R : KFin (s 1) B →ₗ[ℂ] KFin (s 1) B'}
    {L' : KFin (s 0) A' →ₗ[ℂ] KFin (s 0) A''}
    {R' : KFin (s 1) B' →ₗ[ℂ] KFin (s 1) B''}
    (hT : ActsOnTwoCompactFactors s T L R) (hU : ActsOnTwoCompactFactors s U L' R') :
    ActsOnTwoCompactFactors s (U.comp T) (L'.comp L) (R'.comp R) :=
  fun F u v h => hU (T F) (L u) (R v) (hT F u v h)

private def HasReplacementOnTwoFactors (ds es : List RealBlock) (slots : List (Slot N))
    {A A' B B' : List RealBlock} (L : KFin (s 0) A' →ₗ[ℂ] KFin (s 0) A)
    (R : KFin (s 1) B' →ₗ[ℂ] KFin (s 1) B) : Prop :=
  ∃ S : SplitFourierReplacement N ds es, S.slots = slots ∧
    CommutesWithBlockMultipliers (cls s) S.reverse ∧ ActsOnTwoCompactFactors s S.reverse L R

private theorem exists_left_replacement {A A' B : List RealBlock}
    (hA : realRank A = s 0) (hA' : realRank A' = s 0) (hB : realRank B = s 1)
    (L : SplitFourierReplacement (s 0) A A') :
    HasReplacementOnTwoFactors s (A ++ B) (A' ++ B) (L.slots.map (shiftSlot (left_le s)))
      L.reverse (LinearMap.id (M := KFin (s 1) B)) := by
  have ha : realRank ([] : List RealBlock) = start s 0 := (start_zero' s).symm
  have hn : realRank ([] ++ A ++ B) = N := rank_append s hA hB
  have hn' : realRank ([] ++ A' ++ B) = N := rank_append s hA' hB
  refine ⟨L.inStages (left_le s) ha hA hA' hn hn', rfl, ?_, ?_⟩
  · exact ind_commutesWithBlockMultipliers s 0 (left_le s) ha hA' hA hn L.reverse L.reverse_kRep
  · intro F u v hF
    exact ind_left_product s (left_le s) ha hA' hA hn L.reverse L.reverse_kRep F u v.val hF

private theorem exists_right_replacement {A B B' : List RealBlock}
    (hA : realRank A = s 0) (hB : realRank B = s 1) (hB' : realRank B' = s 1)
    (R : SplitFourierReplacement (s 1) B B') :
    HasReplacementOnTwoFactors s (A ++ B) (A ++ B') (R.slots.map (shiftSlot (right_le s)))
      (LinearMap.id (M := KFin (s 0) A)) R.reverse := by
  have ha : realRank A = start s 1 := hA.trans (start_one s).symm
  have hn : realRank (A ++ B ++ []) = N := by rw [List.append_nil]; exact rank_append s hA hB
  have hn' : realRank (A ++ B' ++ []) = N := by rw [List.append_nil]; exact rank_append s hA hB'
  have h : HasReplacementOnTwoFactors s (A ++ B ++ []) (A ++ B' ++ [])
      (R.slots.map (shiftSlot (right_le s))) (LinearMap.id (M := KFin (s 0) A)) R.reverse := by
    refine ⟨R.inStages (right_le s) ha hB hB' hn hn', rfl, ?_, ?_⟩
    · exact ind_commutesWithBlockMultipliers s 1 (right_le s) ha hB' hB hn R.reverse
        R.reverse_kRep
    · intro F u v hF
      exact ind_right_product s (right_le s) ha hB' hB hn R.reverse R.reverse_kRep F u.val v hF
  simpa only [List.append_nil] using h

/-- The composite of the two split replacements has a reverse lift that
commutes with the compact weights and acts on pure products factor by factor. -/
def RealTwoBlockFourierReplacementStatement : Prop :=
  ∀ (s : Fin 2 → ℕ) {A A' B B' : List RealBlock},
    realRank A = s 0 → realRank A' = s 0 → realRank B = s 1 → realRank B' = s 1 →
    ∀ (L : SplitFourierReplacement (s 0) A A') (R : SplitFourierReplacement (s 1) B B'),
      ∃ S : SplitFourierReplacement (∑ i, s i) (A ++ B) (A' ++ B'),
        CommutesWithBlockMultipliers (cls s) S.reverse ∧
        ActsOnTwoCompactFactors s S.reverse L.reverse R.reverse

theorem realTwoBlockFourierReplacement : RealTwoBlockFourierReplacementStatement := by
  intro s A A' B B' hA hA' hB hB' L R
  obtain ⟨L', hLs, hLmult, hLprod⟩ := exists_left_replacement s hA hA' hB L
  obtain ⟨R', hRs, hRmult, hRprod⟩ := exists_right_replacement s hA' hB hB' R
  have hDis : ∀ t ∈ L'.slots, ∀ u ∈ R'.slots, t.Disjoint u := by
    rw [hLs, hRs]
    intro t ht u hu
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp ht
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp hu
    left
    change start s 0 + t.p + 1 < start s 1 + u.p
    rw [start_zero', zero_add, start_one]
    have ht := t.hp
    omega
  refine ⟨L'.compDisjoint R' hDis, hLmult.comp hRmult, ?_⟩
  change ActsOnTwoCompactFactors s (L'.reverse.comp R'.reverse) L.reverse R.reverse
  simpa only [LinearMap.comp_id, LinearMap.id_comp] using
    actsOnTwoCompactFactors_comp s hRprod hLprod

private def HasEquivOnTwoFactors (ds es : List RealBlock)
    {A A' B B' : List RealBlock}
    (L : KFin (s 0) A →ₗ[ℂ] KFin (s 0) A') (R : KFin (s 1) B →ₗ[ℂ] KFin (s 1) B') : Prop :=
  ∃ E : KFin N ds ≃ₗ[ℂ] KFin N es,
    IsRealStandardIntertwiner N (realStandardRep N es) (realStandardLie N es) ds E.toLinearMap ∧
    CommutesWithBlockMultipliers (cls s) E.toLinearMap ∧
    ActsOnTwoCompactFactors s E.toLinearMap L R

private theorem exists_left_equiv {A A' B : List RealBlock}
    (hA : realRank A = s 0) (hA' : realRank A' = s 0) (hB : realRank B = s 1)
    (L : KFin (s 0) A ≃ₗ[ℂ] KFin (s 0) A')
    (hL : IsRealStandardIntertwiner (s 0) (realStandardRep (s 0) A')
      (realStandardLie (s 0) A') A L.toLinearMap) :
    HasEquivOnTwoFactors s (A ++ B) (A' ++ B) L.toLinearMap
      (LinearMap.id (M := KFin (s 1) B)) := by
  have ha : realRank ([] : List RealBlock) = start s 0 := (start_zero' s).symm
  have hn : realRank ([] ++ A' ++ B) = N := rank_append s hA' hB
  let E := standardEquivInd (left_le s) ha hA' hA hn L hL
  have hI := standardEquivInd_intertwiner (left_le s) ha hA' hA hn L hL
  have hK := (isRealStandardIntertwiner_iff.mp hL).1
  refine ⟨E, hI, ind_commutesWithBlockMultipliers s 0 (left_le s) ha hA hA' hn _ hK, ?_⟩
  intro F u v hF
  exact ind_left_product s (left_le s) ha hA hA' hn _ hK F u v.val hF

private theorem exists_right_equiv {A B B' : List RealBlock}
    (hA : realRank A = s 0) (hB : realRank B = s 1) (hB' : realRank B' = s 1)
    (R : KFin (s 1) B ≃ₗ[ℂ] KFin (s 1) B')
    (hR : IsRealStandardIntertwiner (s 1) (realStandardRep (s 1) B')
      (realStandardLie (s 1) B') B R.toLinearMap) :
    HasEquivOnTwoFactors s (A ++ B) (A ++ B') (LinearMap.id (M := KFin (s 0) A))
      R.toLinearMap := by
  have ha : realRank A = start s 1 := hA.trans (start_one s).symm
  have hn : realRank (A ++ B' ++ []) = N := by rw [List.append_nil]; exact rank_append s hA hB'
  let E := standardEquivInd (right_le s) ha hB' hB hn R hR
  have hI := standardEquivInd_intertwiner (right_le s) ha hB' hB hn R hR
  have hK := (isRealStandardIntertwiner_iff.mp hR).1
  have h : HasEquivOnTwoFactors s (A ++ B ++ []) (A ++ B' ++ [])
      (LinearMap.id (M := KFin (s 0) A)) R.toLinearMap := by
    refine ⟨E, hI, ind_commutesWithBlockMultipliers s 1 (right_le s) ha hB hB' hn _ hK, ?_⟩
    intro F u v hF
    exact ind_right_product s (right_le s) ha hB hB' hn _ hK F u.val v hF
  simpa only [List.append_nil] using h

/-- The induced compact equivalence from two actual standard intertwiners
commutes with block weights and acts on pure products by both intertwiners. -/
def RealTwoBlockEquivStatement : Prop :=
  ∀ (s : Fin 2 → ℕ) {A A' B B' : List RealBlock},
    realRank A = s 0 → realRank A' = s 0 → realRank B = s 1 → realRank B' = s 1 →
    ∀ (L : KFin (s 0) A ≃ₗ[ℂ] KFin (s 0) A') (R : KFin (s 1) B ≃ₗ[ℂ] KFin (s 1) B'),
      IsRealStandardIntertwiner (s 0) (realStandardRep (s 0) A')
        (realStandardLie (s 0) A') A L.toLinearMap →
      IsRealStandardIntertwiner (s 1) (realStandardRep (s 1) B')
        (realStandardLie (s 1) B') B R.toLinearMap →
      HasEquivOnTwoFactors s (A ++ B) (A' ++ B') L.toLinearMap R.toLinearMap

theorem realTwoBlockEquiv : RealTwoBlockEquivStatement := by
  intro s A A' B B' hA hA' hB hB' L R hL hR
  obtain ⟨L', hLI, hLmult, hLprod⟩ := exists_left_equiv s hA hA' hB L hL
  obtain ⟨R', hRI, hRmult, hRprod⟩ := exists_right_equiv s hA' hB hB' R hR
  refine ⟨L'.trans R', ?_, hRmult.comp hLmult, ?_⟩
  · obtain ⟨hLK, hLL⟩ := isRealStandardIntertwiner_iff.mp hLI
    obtain ⟨hRK, hRL⟩ := isRealStandardIntertwiner_iff.mp hRI
    apply isRealStandardIntertwiner_iff.mpr
    exact ⟨fun k f => by
      change R' (L' (kRep _ _ k f)) = kRep _ _ k (R' (L' f))
      exact (congrArg R' (hLK k f)).trans (hRK k (L' f)),
      fun X f => by
        change R' (L' (lie _ _ X f)) = lie _ _ X (R' (L' f))
        exact (congrArg R' (hLL X f)).trans (hRL X (L' f))⟩
  · change ActsOnTwoCompactFactors s (R'.toLinearMap.comp L'.toLinearMap) L.toLinearMap
      R.toLinearMap
    simpa only [LinearMap.comp_id, LinearMap.id_comp] using
      actsOnTwoCompactFactors_comp s hLprod hRprod

end Two

/-- Both the split Fourier replacements and the actual standard
equivalences have compatible compact actions under two-factor induction. -/
def RealStandardTwoBlockOperatorsStatement : Prop :=
  RealTwoBlockFourierReplacementStatement ∧ RealTwoBlockEquivStatement

theorem realStandardTwoBlockOperators : RealStandardTwoBlockOperatorsStatement :=
  ⟨realTwoBlockFourierReplacement, realTwoBlockEquiv⟩

end Langlands.Archimedean.InductionStages
