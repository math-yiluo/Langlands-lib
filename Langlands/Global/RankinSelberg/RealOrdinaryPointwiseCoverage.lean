import Langlands.Global.RankinSelberg.RealOrdinaryStrictLeadingDetection
import Langlands.Global.RankinSelberg.RealOrdinaryDualDetection
import Langlands.Global.RankinSelberg.RealNormalizedGenerationInduction
import Langlands.Global.RankinSelberg.RealOrdinaryGenerationPermutation
import Langlands.Global.RankinSelberg.RealAdjacentRankTwoAssembly
import Langlands.Global.RankinSelberg.RealEqualDiscreteGeneration

/-! # Pointwise ordinary normalized generation for real standard models -/

noncomputable section

open Langlands.Archimedean Langlands.LocalFactor.Archimedean
open scoped Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false

namespace Langlands.Global.RankinSelbergGlobal

open ArchimedeanLocal RealNormalizedGenerationInduction
open RealAdjacentRankTwoAssembly (realAdjacentRankTwoAssembly)
open RealEqualDiscreteGeneration (realEqualDiscreteGeneration)
open RealLocalJacquet (dualBlock realRank_map_dualBlock)

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "G" => fun r => Langlands.GeneralLinear (r + 1) ℝ
local notation "Irr[" r "," ds "]" => IsIrreducibleGKModule (realStandardRep (r + 1) ds) (realStandardLie (r + 1) ds)
local notation "L[" ds "," es "]" => realPairLFactor ds es
local notation:max "dual" ds:max => List.map dualBlock ds
local notation "At" => RealOrdinaryPairHasValueAt
local notation "Coef" => fun r => Submodule ℂ (G r → ℂ)

private theorem unequalValue_congr {r t : ℕ} {hrt : t < r} {S S' : Coef r} {T T' : Coef t}
    {L L' : Langlands.LocalFactor.ReciprocalEntire} {μ : RealQuotientMeasureData t} {s : ℂ}
    (hS : S = S') (hT : T = T') (hL : L = L') :
    HasNonzeroOrdinaryNormalizationAt (fun i : S × T => realUnequalIntegral hrt μ i.1 i.2) L s →
    HasNonzeroOrdinaryNormalizationAt (fun i : S' × T' => realUnequalIntegral hrt μ i.1 i.2) L' s := by
  subst S' T' L'
  exact id

private theorem equalValue_congr {r : ℕ} {S S' T T' : Coef r}
    {L L' : Langlands.LocalFactor.ReciprocalEntire} {μ : RealQuotientMeasureData r} {s : ℂ}
    (hS : S = S') (hT : T = T') (hL : L = L') :
    HasNonzeroOrdinaryNormalizationAt (fun i : S × T × 𝓢(Fin (r + 1) → ℝ, ℂ) =>
      realEqualIntegral μ i.1 i.2.1 i.2.2) L s →
    HasNonzeroOrdinaryNormalizationAt (fun i : S' × T' × 𝓢(Fin (r + 1) → ℝ, ℂ) =>
      realEqualIntegral μ i.1 i.2.1 i.2.2) L' s := by
  subst S' T' L'
  exact id

private theorem RealOrdinaryPairHasValueAt.congrModels {r t : ℕ} {ds es ds' es' : List RealBlock}
    {a : ℝˣ} {μ : ∀ k, RealQuotientMeasureData k} {s : ℂ}
    (hD : ∀ b, realWhittakerModel r ds b = realWhittakerModel r ds' b)
    (hE : ∀ b, realWhittakerModel t es b = realWhittakerModel t es' b)
    (hL : L[ds, es] = L[ds', es']) (h : At r t ds es a μ s) : At r t ds' es' a μ s := by
  refine ⟨fun hlt => unequalValue_congr (hD a) (hE (-a)) hL (h.1 hlt), ?_, ?_⟩
  · intro hlt
    have heq : L[es, ds] = L[es', ds'] := (realPairLFactor_comm es ds).trans (hL.trans (realPairLFactor_comm ds' es'))
    exact unequalValue_congr (hE (-a)) (hD (-(-a))) heq (h.2.1 hlt)
  · intro heq
    subst t
    exact equalValue_congr (hD a) (hE (-a)) hL (h.2.2 rfl)

private theorem RealOrdinaryPairHasValueAt.reflect (hO : RealOrdinaryNormalizedContinuationStatement)
    {r t : ℕ} {ds es : List RealBlock} (hd : realRank ds = r + 1) (he : realRank es = t + 1)
    (hdI : Irr[r, ds]) (heI : Irr[t, es]) {a : ℝˣ} {μ : ∀ k, RealQuotientMeasureData k} {s : ℂ}
    (h : At r t (dual ds) (dual es) (-a) μ (1 - s)) : At r t ds es a μ s := by
  refine ⟨fun hlt => (realOrdinaryDualDetection hO).1 r t hlt ds es hd he hdI heI a (μ t) s (h.1 hlt), ?_, ?_⟩
  · intro hlt
    exact (realOrdinaryDualDetection hO).1 t r hlt es ds he hd heI hdI (-a) (μ r) s (h.2.1 hlt)
  · intro hEq
    subst t
    exact (realOrdinaryDualDetection hO).2 r ds es hd he hdI heI a (μ r) s (h.2.2 rfl)

private theorem realRank_pos_of_ne_nil {ds : List RealBlock} (hd : ds ≠ []) : 0 < realRank ds := by
  cases ds with
  | nil => exact (hd rfl).elim
  | cons x xs =>
    have hx : 0 < realRank [x] := by cases x <;> exact Nat.succ_pos _
    change 0 < realRank ([x] ++ xs)
    rw [realRank_append]
    omega

private theorem realRank_ne_nil {r : ℕ} {ds : List RealBlock} (hd : realRank ds = r + 1) : ds ≠ [] := by
  rintro rfl
  exact (Nat.succ_ne_zero r) hd.symm

private theorem irreducibleSublist {r t : ℕ} {ds es : List RealBlock} (hd : realRank ds = r + 1)
    (he : realRank es = t + 1) (hsub : es.Sublist ds) (ho : Langlands.Archimedean.IsRealLanglandsOrdered ds)
    (hI : Irr[r, ds]) : Irr[t, es] := by
  let P (xs : List RealBlock) (k : ℕ) := IsIrreducibleGKModule (realStandardRep k xs) (realStandardLie k xs)
  have hdI : P ds (realRank ds) := (congrArg (P ds) hd).mpr hI
  exact (congrArg (P es) he).mp (realStandardIrreducibleSublist ds es hsub ho hdI)

private theorem rank_split {r m p : ℕ} {ds d₁ d₂ : List RealBlock} (hd : realRank ds = r + 1)
    (h₁ : realRank d₁ = m + 1) (h₂ : realRank d₂ = p + 1) (hPerm : ds.Perm (d₂ ++ d₁)) :
    r = p + 1 + m := by
  have h := realRank_perm hPerm
  rw [realRank_append, hd, h₁, h₂] at h
  omega

private theorem RealOrdinaryPairHasValueAt.liftPermuted (hO : RealOrdinaryNormalizedContinuationStatement)
    {r t m p : ℕ} {ds es d₁ d₂ : List RealBlock} (hd : realRank ds = r + 1)
    (he : realRank es = t + 1) (h₁ : realRank d₁ = m + 1) (h₂ : realRank d₂ = p + 1)
    (hPerm : ds.Perm (d₂ ++ d₁)) (hdI : Irr[r, ds])
    {a : ℝˣ} {μ : ∀ k, RealQuotientMeasureData k} {s : ℂ}
    (hDen : L[d₂, es].denominator s ≠ 0) (h : At m t d₁ es a μ s) : At r t ds es a μ s := by
  have hr := rank_split hd h₁ h₂ hPerm
  subst r
  have hW := (realWhittakerModels_of_perm_irreducible hPerm hd hdI).2
  exact (h.leadingLift hO h₁ h₂ he hDen).congrModels hW (fun _ => rfl)
    (realPairLFactor_perm hPerm (List.Perm.refl _)).symm

private theorem singletonPairValue (r t : ℕ) (x y : RealBlock)
    (hx : realRank [x] = r + 1) (hy : realRank [y] = t + 1)
    (hxI : Irr[r, [x]]) (hyI : Irr[t, [y]])
    (hxW : ∀ d, RealBlock.induced d = x → 0 < d.weight)
    (hyW : ∀ d, RealBlock.induced d = y → 0 < d.weight)
    (a : ℝˣ) (μ : ∀ k, RealQuotientMeasureData k) (s : ℂ) : At r t [x] [y] a μ s := by
  cases x with
  | character c =>
    have hr : r = 0 := by change 1 = r + 1 at hx; omega
    subst r
    cases y with
    | character d =>
      have ht : t = 0 := by change 1 = t + 1 at hy; omega
      subst t
      have h := (rankOneOrdinaryNormalizedTests.1 [.character c] [.character d] rfl rfl a (μ 0)).2
        (realWhittakerModel_ne_bot_of_rank 0 _ rfl a) (realWhittakerModel_ne_bot_of_rank 0 _ rfl (-a))
      exact .of_equal (HasFiniteOrdinaryNormalizationSum.covering
        (realOrdinaryEqualTest 0 [.character c] [.character d] a (μ 0)) _ h s)
    | induced d =>
      have ht : t = 1 := by change 2 = t + 1 at hy; omega
      subst t
      have h := (RealOrdinaryPairHasValueAt.of_unequal (Nat.lt_succ_self 0)
        ((realAdjacentRankTwoAssembly [.induced d] [.character c] rfl rfl hyI (-a) (μ 0)).1 s)).swap
      rw [show -(-a) = a from neg_neg a] at h
      exact h
  | induced c =>
    have hr : r = 1 := by change 2 = r + 1 at hx; omega
    subst r
    cases y with
    | character d =>
      have ht : t = 0 := by change 1 = t + 1 at hy; omega
      subst t
      exact .of_unequal (Nat.lt_succ_self 0) ((realAdjacentRankTwoAssembly [.induced c] [.character d] rfl rfl hxI a (μ 0)).1 s)
    | induced d =>
      have ht : t = 1 := by change 2 = t + 1 at hy; omega
      subst t
      exact .of_equal ((realEqualDiscreteGeneration c d (hxW c rfl).ne' (hyW d rfl).ne' hxI hyI a (μ 1)).1 s)

local notation "Below" => fun (n : ℕ) =>
  ∀ (r t : ℕ), r + t < n → ∀ (ds es : List RealBlock), realRank ds = r + 1 → realRank es = t + 1 →
    Irr[r, ds] → Irr[t, es] → ∀ (a : ℝˣ) (μ : ∀ k, RealQuotientMeasureData k) (s : ℂ), At r t ds es a μ s

set_option maxHeartbeats 1050000 in
private theorem pointwise_of_append (hO : RealOrdinaryNormalizedContinuationStatement)
    (r t : ℕ) (xs ys : List RealBlock) (x y : RealBlock) (hx : xs ≠ [])
    (hd : realRank (xs ++ [x]) = r + 1) (he : realRank (y :: ys) = t + 1)
    (hdo : Langlands.Archimedean.IsRealLanglandsOrdered (xs ++ [x])) (heo : Langlands.Archimedean.IsRealLanglandsOrdered (y :: ys))
    (hdI : Irr[r, xs ++ [x]]) (heI : Irr[t, y :: ys])
    (ih : Below (r + t)) (a : ℝˣ) (μ : ∀ k, RealQuotientMeasureData k) (s : ℂ) :
    At r t (xs ++ [x]) (y :: ys) a μ s := by
  have hrx : 0 < realRank xs := realRank_pos_of_ne_nil hx
  have hxx : 0 < realRank [x] := realRank_pos_of_ne_nil (by simp)
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hrx.ne'
  obtain ⟨p, hp⟩ := Nat.exists_eq_succ_of_ne_zero hxx.ne'
  change realRank xs = m + 1 at hm
  change realRank [x] = p + 1 at hp
  have hSplit : r = p + 1 + m := rank_split hd hm hp List.perm_append_comm
  have hXsI := irreducibleSublist hd hm (List.sublist_append_left xs [x]) hdo hdI
  have hmin : ∀ z ∈ xs, realBlockExponent x ≤ realBlockExponent z :=
    fun z hz => (List.pairwise_append.mp hdo).2.2 z hz x (by simp)
  have hReflect (hDen : L[[dualBlock x], dual (y :: ys)].denominator (1 - s) ≠ 0) :
      At r t (xs ++ [x]) (y :: ys) a μ s := by
    have hdm := (realRank_map_dualBlock xs).trans hm
    have hdq := (realRank_map_dualBlock [x]).trans hp
    have hdt := (realRank_map_dualBlock (y :: ys)).trans he
    have hdr := (realRank_map_dualBlock (xs ++ [x])).trans hd
    have hmI := (realBlockWhittakerDual m xs hm hXsI).1
    have hrI := (realBlockWhittakerDual r (xs ++ [x]) hd hdI).1
    have htI := (realBlockWhittakerDual t (y :: ys) he heI).1
    have hLower := ih m t (by omega) (dual xs) (dual (y :: ys)) hdm hdt hmI htI (-a) μ (1 - s)
    have hPerm : (dual (xs ++ [x])).Perm ([dualBlock x] ++ dual xs) := by
      rw [List.map_append, List.map_singleton]
      exact List.perm_append_comm
    exact (hLower.liftPermuted hO hdr hdt hdm hdq hPerm hrI hDen).reflect hO hd he hdI heI
  by_cases hy : ys = []
  · subst ys
    rcases primal_or_reflected_ne_zero (y := y) hmin s with hDen | hDen
    · have hXI := irreducibleSublist hd hp (List.sublist_append_right xs [x]) hdo hdI
      have hLower := ih p t (by omega) [x] [y] hp he hXI heI a μ s
      exact hLower.liftPermuted hO hd he hp hm (List.Perm.refl _) hdI hDen
    · exact hReflect hDen
  · have hmax : ∀ z ∈ ys, realBlockExponent z ≤ realBlockExponent y := (List.pairwise_cons.mp heo).1
    rcases extreme_or_reflected_ne_zero hmin hmax s with hDen | hDen
    · have hry : 0 < realRank ys := realRank_pos_of_ne_nil hy
      have hyy : 0 < realRank [y] := realRank_pos_of_ne_nil (by simp)
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hry.ne'
      obtain ⟨q, hq⟩ := Nat.exists_eq_succ_of_ne_zero hyy.ne'
      change realRank ys = k + 1 at hk
      change realRank [y] = q + 1 at hq
      have hCut := rank_split he hk hq (show (y :: ys).Perm ([y] ++ ys) from List.Perm.refl _)
      have hYsI := irreducibleSublist he hk (List.sublist_cons_self y ys) heo heI
      have hLower := ih k r (by omega) ys (xs ++ [x]) hk hd hYsI hdI (-a) μ s
      rw [realPairLFactor_comm (xs ++ [x]) [y]] at hDen
      have hUpper := (hLower.liftPermuted hO he hd hk hq (List.Perm.refl _) heI hDen).swap
      rw [show -(-a) = a from neg_neg a] at hUpper
      exact hUpper
    · exact hReflect hDen

private theorem pointwise_of_ordered (hO : RealOrdinaryNormalizedContinuationStatement)
    (r t : ℕ) (ds es : List RealBlock) (hd : realRank ds = r + 1) (he : realRank es = t + 1)
    (hdI : Irr[r, ds]) (heI : Irr[t, es])
    (hdo : Langlands.Archimedean.IsRealLanglandsOrdered ds) (heo : Langlands.Archimedean.IsRealLanglandsOrdered es)
    (hdw : ∀ d, RealBlock.induced d ∈ ds → 0 < d.weight)
    (hew : ∀ d, RealBlock.induced d ∈ es → 0 < d.weight)
    (ih : Below (r + t)) (a : ℝˣ) (μ : ∀ k, RealQuotientMeasureData k) (s : ℂ) : At r t ds es a μ s := by
  rcases ds.eq_nil_or_concat' with hNil | ⟨xs, x, hd'⟩
  · exact (realRank_ne_nil hd hNil).elim
  subst ds
  cases es with
  | nil => exact (realRank_ne_nil he rfl).elim
  | cons y ys =>
    by_cases hx : xs = []
    · subst xs
      rcases (y :: ys).eq_nil_or_concat' with hNil | ⟨zs, z, hEq⟩
      · exact (List.cons_ne_nil _ _ hNil).elim
      by_cases hz : zs = []
      · subst zs
        have heq : y :: ys = [z] := hEq
        rw [heq] at he heI hew ⊢
        exact singletonPairValue r t x z hd he hdI heI (fun d h => hdw d (by simp [h]))
          (fun d h => hew d (by simp [h])) a μ s
      · rw [hEq] at he heI heo ⊢
        have hi : Below (t + r) := by rw [add_comm t r]; exact ih
        have h := (pointwise_of_append hO t r zs [] z x hz he hd heo hdo heI hdI hi (-a) μ s).swap
        rw [show -(-a) = a from neg_neg a] at h
        exact h
    · exact pointwise_of_append hO r t xs ys x y hx hd he hdo heo hdI heI ih a μ s

set_option maxHeartbeats 900000 in
/-- Every pair of rank-correct irreducible real models has an exact nonzero normalized
test at the specified spectral point, using a family of compatible measures. -/
theorem realOrdinaryPairValueAt (hO : RealOrdinaryNormalizedContinuationStatement) :
    ∀ (r t : ℕ) (ds es : List RealBlock), realRank ds = r + 1 → realRank es = t + 1 →
      Irr[r, ds] → Irr[t, es] → ∀ (a : ℝˣ) (μ : ∀ k, RealQuotientMeasureData k) (s : ℂ), At r t ds es a μ s := by
  suffices h : ∀ (n r t : ℕ), r + t = n → ∀ (ds es : List RealBlock), realRank ds = r + 1 → realRank es = t + 1 →
      Irr[r, ds] → Irr[t, es] → ∀ (a : ℝˣ) (μ : ∀ k, RealQuotientMeasureData k) (s : ℂ), At r t ds es a μ s from
    fun r t => h (r + t) r t rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro r t hrt ds es hd he hdI heI a μ s
    obtain ⟨d, hdr, hdo, hdw, hdi, hdW, hdL⟩ := exists_positiveWeight_ordered_model r ds hd hdI
    obtain ⟨e, her, heo, hew, hei, heW, heL⟩ := exists_positiveWeight_ordered_model t es he heI
    have hBelow : Below (r + t) := fun k l hlt => ih (k + l) (hrt ▸ hlt) k l rfl
    have h := pointwise_of_ordered hO r t d e hdr her hdi hei hdo heo hdw hew hBelow a μ s
    have hL : L[d, e] = L[ds, es] := by
      rw [hdL e, realPairLFactor_comm ds e, heL ds, realPairLFactor_comm es ds]
    exact h.congrModels hdW heW hL

/-- Exact ordinary continuation implies pointwise normalized generation for the supplied
coefficient models and measure, in both ordinary real integral families. -/
def RealOrdinaryPointwiseCoverageStatement : Prop :=
  RealOrdinaryNormalizedContinuationStatement →
  (∀ (r t : ℕ) (h : t < r) (ds es : List RealBlock), realRank ds = r + 1 → realRank es = t + 1 →
    Irr[r, ds] → Irr[t, es] → ∀ (a : ℝˣ) (D : RealQuotientMeasureData t),
      HasCoveringOrdinaryNormalizations (realOrdinaryUnequalTest h ds es a D) L[ds, es]) ∧
  ∀ (r : ℕ) (ds es : List RealBlock), realRank ds = r + 1 → realRank es = r + 1 →
    Irr[r, ds] → Irr[r, es] → ∀ (a : ℝˣ) (D : RealQuotientMeasureData r),
      HasCoveringOrdinaryNormalizations (realOrdinaryEqualTest r ds es a D) L[ds, es]

private theorem exists_measureFamily (a : ℝˣ) (r : ℕ) (D : RealQuotientMeasureData r) :
    ∃ μ : ∀ k, RealQuotientMeasureData k, μ r = D := by
  refine ⟨fun k => if h : k = r then h.symm ▸ D else (RealGodement.nonempty_realQuotientMeasureData k a).some, ?_⟩
  simp only [dite_eq_left]

theorem realOrdinaryPointwiseCoverage : RealOrdinaryPointwiseCoverageStatement := by
  intro hO
  constructor
  · intro r t h ds es hd he hdI heI a D s
    obtain ⟨μ, hμ⟩ := exists_measureFamily a t D
    have hAt := (realOrdinaryPairValueAt hO r t ds es hd he hdI heI a μ s).1 h
    have hTest := congrArg (fun Q => HasNonzeroOrdinaryNormalizationAt
      (realOrdinaryUnequalTest h ds es a Q) L[ds, es] s) hμ
    exact hTest.mp hAt
  · intro r ds es hd he hdI heI a D s
    obtain ⟨μ, hμ⟩ := exists_measureFamily a r D
    have hAt := (realOrdinaryPairValueAt hO r r ds es hd he hdI heI a μ s).2.2 rfl
    have hTest := congrArg (fun Q => HasNonzeroOrdinaryNormalizationAt
      (realOrdinaryEqualTest r ds es a Q) L[ds, es] s) hμ
    exact hTest.mp hAt

end Langlands.Global.RankinSelbergGlobal
