import Langlands.Representation.Archimedean.RealStandardAnnihilatorGrowth
import Langlands.Representation.Archimedean.RealLinkedQuotientAnnihilator
import Langlands.Representation.Archimedean.RealPrincipalSeriesInfinitesimalCharacter

/-!
# A quotient of slow growth of a linked real standard module

`RealLinkedQuotientGrowthStatement`: for a Langlands-ordered list `ds` of real blocks of total
rank `n` with two linked Mœglin data, the `O(n)`-finite functions `I(ds)` of the standard module
have a proper `(𝔤, K)`-submodule `W` such that the elements of degree at most `d` of `U(𝔤)` act
on the quotient `I(ds) / W` through a space of dimension at most `C (d + 1)^(n (n - 1) - 1)`.

`realLinkedStandardQuotientAnnihilator_of_growth` proves that this statement and
`RealStandardAnnihilatorGrowthStatement` imply `RealLinkedStandardQuotientAnnihilatorStatement`,
and `realLinkedLanglandsQuotientNotLarge_of_growth` that they imply the Library statement
`RealLinkedLanglandsQuotientNotLargeStatement`.
-/

noncomputable section

open scoped TensorProduct

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean Langlands.Algebra.UniversalEnveloping

/-- **A quotient of slow growth.** For a list `ds` of real blocks of total rank `n` in Langlands
order, two of whose Mœglin data are linked, the `O(n)`-finite functions of the standard module
of `ds` have a proper `(𝔤, K)`-submodule `W` and a constant `C` such that for every `d` the
operators `v ↦ u v mod W` from `I(ds)` to `I(ds) / W`, for `u` of degree at most `d` in
`U(ℂ ⊗_ℝ 𝔤𝔩_n(ℝ))`, span a space of dimension at most `C (d + 1)^(n (n - 1) - 1)`. -/
def RealLinkedQuotientGrowthStatement : Prop :=
  ∀ (n : ℕ) (ds : List RealBlock), realRank ds = n → IsRealLanglandsOrdered ds →
    ¬ IsRealMoeglinUnlinked ds →
      ∃ W : Submodule ℂ (kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)),
        IsGKSubmodule (realStandardRep n ds) (realStandardLie n ds) W ∧ W ≠ ⊤ ∧
        ∃ C : ℝ, ∀ d : ℕ,
          (Module.finrank ℂ ((degreeFiltration ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) d).map
            (LinearMap.llcomp ℂ _ _ _ W.mkQ ∘ₗ
              (envelopingAction (realStandardLie n ds)).toLinearMap)) : ℝ) ≤
            C * ((d : ℝ) + 1) ^ (n * (n - 1) - 1)

namespace RealLinkedQuotientGrowth

/-- A linked pair needs two Mœglin data, hence total rank at least `2`. -/
theorem two_le_of_not_unlinked {n : ℕ} {ds : List RealBlock} (hrank : realRank ds = n)
    (hlink : ¬ IsRealMoeglinUnlinked ds) : 2 ≤ n := by
  have hlen : ∀ ds : List RealBlock, (realMoeglinData ds).length ≤ realRank ds := by
    intro ds
    induction ds with
    | nil => simp [realMoeglinData, realRank]
    | cons b ds ih =>
      have hb : (realBlockMoeglinData b).length ≤ b.rank := by
        cases b with
        | character d => simp [realBlockMoeglinData, RealBlock.rank]
        | induced d =>
          simp only [realBlockMoeglinData, RealBlock.rank]
          split_ifs <;> simp
      simp only [realMoeglinData, List.flatMap_cons, List.length_append, realRank,
        List.map_cons, List.sum_cons] at ih ⊢
      omega
  by_contra h
  apply hlink
  have h1 : (realMoeglinData ds).length ≤ 1 := by
    have := hlen ds
    omega
  unfold IsRealMoeglinUnlinked
  match hl : realMoeglinData ds, h1 with
  | [], _ => exact List.Pairwise.nil
  | [_], _ => exact List.pairwise_singleton _ _
  | _ :: _ :: _, h1 => simp at h1

/-- A linear map injective on a subspace `P` maps it onto a space of the same finite rank. -/
theorem finrank_map_eq_of_injOn {K E F : Type*} [Field K] [AddCommMonoid E] [Module K E]
    [AddCommMonoid F] [Module K F] (T : E →ₗ[K] F) (P : Submodule K E)
    (h : Set.InjOn T P) :
    Module.finrank K (P.map T) = Module.finrank K P := by
  have hinj : Function.Injective (T.domRestrict P) := fun x y hxy =>
    Subtype.ext (h x.2 y.2 hxy)
  rw [← LinearMap.range_domRestrict]
  exact (LinearEquiv.ofInjective _ hinj).finrank_eq.symm

/-- A polynomial bound of exponent `N - 1` cannot dominate a lower bound of exponent `N ≥ 1`
for all `d`. -/
theorem not_forall_le {c C : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) {a b : ℕ → ℝ}
    (hlow : ∀ d : ℕ, c * ((d : ℝ) + 1) ^ N ≤ a d)
    (hup : ∀ d : ℕ, b d ≤ C * ((d : ℝ) + 1) ^ (N - 1)) (hab : ∀ d, a d ≤ b d) : False := by
  set d : ℕ := ⌈C / c⌉₊
  have hpos : (0 : ℝ) < ((d : ℝ) + 1) ^ (N - 1) := by positivity
  have hdc : C < c * ((d : ℝ) + 1) := by
    have h1 : C / c ≤ (d : ℝ) := Nat.le_ceil _
    have h2 : C / c < (d : ℝ) + 1 := by linarith
    rwa [div_lt_iff₀ hc, mul_comm] at h2
  have hpow : ((d : ℝ) + 1) ^ N = ((d : ℝ) + 1) * ((d : ℝ) + 1) ^ (N - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hN]
  have := (hlow d).trans ((hab d).trans (hup d))
  rw [hpow, ← mul_assoc] at this
  have := (mul_lt_mul_of_pos_right hdc hpos)
  linarith

end RealLinkedQuotientGrowth

open RealLinkedQuotientGrowth in
/-- **The reduction.** The growth lower bound for real standard modules and the slow growth of
a quotient of a linked one give a proper quotient with a strictly larger annihilator. -/
theorem realLinkedStandardQuotientAnnihilator_of_growth
    (hL : RealStandardAnnihilatorGrowthStatement) (hU : RealLinkedQuotientGrowthStatement) :
    RealLinkedStandardQuotientAnnihilatorStatement := by
  intro n ds hrank hord hlink
  obtain ⟨W, hWgk, hWtop, C, hC⟩ := hU n ds hrank hord hlink
  obtain ⟨c, hc, hcd⟩ := hL n ds hrank
  refine ⟨W, hWgk, hWtop, ?_⟩
  by_contra hne
  push Not at hne
  have hn := two_le_of_not_unlinked hrank hlink
  have hN : 1 ≤ n * (n - 1) := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hker : ∀ u, (LinearMap.llcomp ℂ _ _ _ W.mkQ :
      Module.End ℂ (kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)) →ₗ[ℂ]
        (_ →ₗ[ℂ] _ ⧸ W)) ((envelopingAction (realStandardLie n ds)).toLinearMap u) = 0 →
      (envelopingAction (realStandardLie n ds)).toLinearMap u = 0 := by
    intro u hu
    refine hne u fun v => ?_
    have := LinearMap.congr_fun hu v
    rwa [LinearMap.llcomp_apply, LinearMap.zero_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero] at this
  refine not_forall_le hc hN hcd hC fun d => le_of_eq ?_
  rw [Submodule.map_comp]
  refine congrArg Nat.cast (finrank_map_eq_of_injOn _ _ ?_).symm
  rintro _ ⟨a, -, rfl⟩ _ ⟨b, -, rfl⟩ hab
  have h0 := hker (a - b) (by rw [map_sub, map_sub, hab, sub_self])
  rwa [map_sub, sub_eq_zero] at h0

/-- **Non-largeness of linked real Langlands quotients from the two growth statements.** -/
theorem realLinkedLanglandsQuotientNotLarge_of_growth
    (hL : RealStandardAnnihilatorGrowthStatement) (hU : RealLinkedQuotientGrowthStatement) :
    RealLinkedLanglandsQuotientNotLargeStatement :=
  realLinkedLanglandsQuotientNotLarge_of_quotientAnnihilator
    realStandardLie_hasInfinitesimalCharacter
    (realLinkedStandardQuotientAnnihilator_of_growth hL hU)

end Langlands.Archimedean
