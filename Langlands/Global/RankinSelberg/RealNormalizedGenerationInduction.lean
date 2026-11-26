import Langlands.Representation.Archimedean.RealPairLFactorRegularityProof
import Langlands.Global.RankinSelberg.RealLocalWhittakerModel
import Langlands.LocalFactor.ArchimedeanPairFactor
import Langlands.Representation.Archimedean.RealGenericParameterReduction
import Mathlib.Data.List.Pairwise

/-! # Pointwise induction for real normalized generation -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealNormalizedGenerationInduction

open Langlands.Archimedean Langlands.LocalFactor.Archimedean
open RealLocalJacquet (dualBlock)

private theorem exponent_dual (x : RealBlock) :
    realBlockExponent (dualBlock x) = -realBlockExponent x := by
  cases x <;> simp [dualBlock, realBlockExponent, RealCharacterData.inverse,
    ComplexCharacterData.inverse, Complex.neg_re]

/-- A real pair denominator is nonzero when the real part of the spectral
parameter plus each sum of block exponents is positive. -/
theorem pairDenominator_ne_zero {xs ys : List RealBlock} {s : ℂ}
    (h : ∀ x ∈ xs, ∀ y ∈ ys, 0 < s.re + realBlockExponent x + realBlockExponent y) :
    (realPairLFactor xs ys).denominator s ≠ 0 :=
  Langlands.Archimedean.realPairLFactorRightHalfPlaneRegularity xs ys s h

private theorem reflectedPairDenominator_ne_zero {x : RealBlock} {ys : List RealBlock} {s : ℂ}
    (h : ∀ y ∈ ys, s.re + realBlockExponent x + realBlockExponent y < 1) :
    (realPairLFactor [dualBlock x] (ys.map dualBlock)).denominator (1 - s) ≠ 0 := by
  apply pairDenominator_ne_zero
  intro z hz w hw
  obtain rfl : z = dualBlock x := by simpa using hz
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hw
  simp only [Complex.sub_re, Complex.one_re, exponent_dual]
  linarith [h y hy]

/-- The two complementary denominators in the real single-right-block
induction have no common zero when `x` is the least-exponent left block. -/
theorem primal_or_reflected_ne_zero {xs : List RealBlock} {x y : RealBlock}
    (hx : ∀ z ∈ xs, realBlockExponent x ≤ realBlockExponent z) (s : ℂ) :
    (realPairLFactor xs [y]).denominator s ≠ 0 ∨
    (realPairLFactor [dualBlock x] [dualBlock y]).denominator (1 - s) ≠ 0 := by
  by_cases h : 0 < s.re + realBlockExponent x + realBlockExponent y
  · left
    apply pairDenominator_ne_zero
    intro z hz w hw
    obtain rfl : w = y := by simpa using hw
    linarith [hx z hz]
  · right
    apply reflectedPairDenominator_ne_zero (ys := [y])
    intro z hz
    obtain rfl : z = y := by simpa using hz
    linarith

/-- With two lists, the denominator for the largest-exponent right block
has no common zero with the reflected denominator for the smallest-exponent
left block. -/
theorem extreme_or_reflected_ne_zero {xs ys : List RealBlock} {x y : RealBlock}
    (hx : ∀ z ∈ xs, realBlockExponent x ≤ realBlockExponent z)
    (hy : ∀ z ∈ ys, realBlockExponent z ≤ realBlockExponent y) (s : ℂ) :
    (realPairLFactor (xs ++ [x]) [y]).denominator s ≠ 0 ∨
    (realPairLFactor [dualBlock x] ((y :: ys).map dualBlock)).denominator (1 - s) ≠ 0 := by
  by_cases h : 0 < s.re + realBlockExponent x + realBlockExponent y
  · left
    apply pairDenominator_ne_zero
    intro z hz w hw
    obtain rfl : w = y := by simpa using hw
    rcases List.mem_append.mp hz with hz | hz
    · linarith [hx z hz]
    · obtain rfl : z = x := by simpa using hz
      exact h
  · right
    apply reflectedPairDenominator_ne_zero
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · linarith
    · linarith [hy z hz]

/-- Evaluation of some member of the function space is nonzero at every point. -/
def Covers (M : Submodule ℂ (ℂ → ℂ)) : Prop :=
  ∀ s : ℂ, ∃ f ∈ M, f s ≠ 0

/-- A family of spaces covers every ordered pair of nonempty lists if it covers
single-block pairs and admits the indicated inclusions after normalization.
The multipliers are the complementary primal and reflected dual denominators. -/
def RealNormalizedGenerationInductionStatement : Prop :=
  ∀ M : List RealBlock → List RealBlock → Submodule ℂ (ℂ → ℂ),
    (∀ x y, Covers (M [x] [y])) →
    (∀ x ys, ys ≠ [] → IsRealLanglandsOrdered ys → Covers (M ys [x]) → Covers (M [x] ys)) →
    (∀ x xs y, xs ≠ [] → IsRealLanglandsOrdered (xs ++ [x]) →
      ∀ f ∈ M [x] [y],
        (fun s => (realPairLFactor xs [y]).denominator s * f s) ∈ M (xs ++ [x]) [y]) →
    (∀ x xs ys, xs ≠ [] → ys ≠ [] → IsRealLanglandsOrdered (xs ++ [x]) →
      IsRealLanglandsOrdered ys → ∀ f ∈ M xs ys,
        (fun s => (realPairLFactor [dualBlock x] (ys.map dualBlock)).denominator (1 - s) * f s) ∈
          M (xs ++ [x]) ys) →
    (∀ xs y ys, xs ≠ [] → ys ≠ [] → IsRealLanglandsOrdered xs → IsRealLanglandsOrdered (y :: ys) →
      ∀ f ∈ M xs ys, (fun s => (realPairLFactor xs [y]).denominator s * f s) ∈ M xs (y :: ys)) →
    ∀ xs ys, xs ≠ [] → ys ≠ [] → IsRealLanglandsOrdered xs → IsRealLanglandsOrdered ys → Covers (M xs ys)

theorem realNormalizedGenerationInduction : RealNormalizedGenerationInductionStatement := by
  intro M hBase hInterchange hFirst hSecond hThird
  have hSingleRight (ds : List RealBlock) (y : RealBlock) :
      ds ≠ [] → IsRealLanglandsOrdered ds → Covers (M ds [y]) := by
    induction ds using List.reverseRecOn with
    | nil => exact fun h => (h rfl).elim
    | append_singleton xs x ih =>
      intro _ hd s
      by_cases hx : xs = []
      · subst xs
        exact hBase x y s
      have hd' := List.pairwise_append.mp hd
      have hmin : ∀ z ∈ xs, realBlockExponent x ≤ realBlockExponent z :=
        fun z hz => hd'.2.2 z hz x (by simp)
      rcases primal_or_reflected_ne_zero hmin s with h | h
      · obtain ⟨f, hf, hn⟩ := hBase x y s
        exact ⟨_, hFirst x xs y hx hd f hf, mul_ne_zero h hn⟩
      · obtain ⟨f, hf, hn⟩ := ih hx hd'.1 s
        exact ⟨_, hSecond x xs [y] hx (by simp) hd (List.pairwise_singleton _ y) f hf, mul_ne_zero h hn⟩
  suffices h : ∀ (n : ℕ) (xs ys : List RealBlock), xs.length + ys.length = n →
      xs ≠ [] → ys ≠ [] → IsRealLanglandsOrdered xs → IsRealLanglandsOrdered ys → Covers (M xs ys) from
    fun xs ys => h _ xs ys rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro ds es hlen hds hes hd he s
    rcases ds.eq_nil_or_concat' with rfl | ⟨xs, x, rfl⟩
    · exact (hds rfl).elim
    by_cases hx : xs = []
    · subst xs
      exact hInterchange x es hes he (hSingleRight es x hes he) s
    have hd' := List.pairwise_append.mp hd
    have hmin : ∀ z ∈ xs, realBlockExponent x ≤ realBlockExponent z :=
      fun z hz => hd'.2.2 z hz x (by simp)
    have hX : IsRealLanglandsOrdered xs := hd'.1
    have hSmaller : Covers (M xs es) :=
      ih (xs.length + es.length) (by simp only [List.length_append, List.length_singleton] at hlen; omega)
        xs es rfl hx hes hX he
    have hDual : (realPairLFactor [dualBlock x] (es.map dualBlock)).denominator (1 - s) ≠ 0 →
        ∃ f ∈ M (xs ++ [x]) es, f s ≠ 0 := by
      intro h
      obtain ⟨f, hf, hn⟩ := hSmaller s
      exact ⟨_, hSecond x xs es hx hes hd he f hf, mul_ne_zero h hn⟩
    cases es with
    | nil => exact (hes rfl).elim
    | cons y ys =>
      by_cases hy : ys = []
      · subst ys
        exact hSingleRight (xs ++ [x]) y hds hd s
      · have he' := List.pairwise_cons.mp he
        have hmax : ∀ z ∈ ys, realBlockExponent z ≤ realBlockExponent y := he'.1
        have hY : IsRealLanglandsOrdered ys := he'.2
        rcases extreme_or_reflected_ne_zero hmin hmax s with h | h
        · have hSmallerRight := ih ((xs ++ [x]).length + ys.length) (by simp at hlen; simp; omega)
            (xs ++ [x]) ys rfl hds hy hd hY
          obtain ⟨f, hf, hn⟩ := hSmallerRight s
          exact ⟨_, hThird (xs ++ [x]) y ys hds hy hd he f hf, mul_ne_zero h hn⟩
        · exact hDual h

end Langlands.Global.RankinSelbergGlobal.RealNormalizedGenerationInduction
