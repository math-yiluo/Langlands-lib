import Langlands.Representation.Whittaker.BruhatCompatibleSupportStatement
import Langlands.Representation.Whittaker.BruhatFiberCharacterCovarianceProof
import Langlands.HarmonicAnalysis.Distribution.CharacterAverageSurjectiveProof
import Langlands.Representation.Twist.ContinuousCharacterProof

/-!
# Proof of support on the compatible torus from fiber invariance

Proves `Langlands.Whittaker.BruhatCompatibleSupportStatement`. Covariance of the character
average under the fiber action turns the invariance hypothesis into `τ (δ⁻¹ · g) = τ g`
for every test function `g` on `H = Fin (n + 1) → Fˣ`, where `δ` is a compatibility
defect; surjectivity of the average supplies every `g`. Off the compatible torus some
defect is locally constant and different from one near each point, so `τ` kills test
functions supported there; a finite clopen cover of the compact support and finite
linearity finish the proof. See the paired Markdown.
-/

noncomputable section

namespace Langlands.Whittaker

open MeasureTheory Langlands.GeneralLinear Langlands.HarmonicAnalysis

universe uF

namespace BruhatCompatibleSupport

section Cutoff

variable {X : Type*} [TopologicalSpace X]

/-- The product of a test function with the indicator function of a clopen set. -/
def clopenCutoff {V : Set X} (hV : IsClopen V) (f : SchwartzBruhat X) : SchwartzBruhat X :=
  ⟨fun x => LocallyConstant.charFn ℂ hV x * f x,
    (LocallyConstant.charFn ℂ hV).isLocallyConstant.comp₂ f.locallyConstant (· * ·),
    f.hasCompactSupport.mul_left⟩

theorem clopenCutoff_apply_of_mem {V : Set X} (hV : IsClopen V) (f : SchwartzBruhat X)
    {x : X} (hx : x ∈ V) : clopenCutoff hV f x = f x := by
  change V.indicator (fun _ => (1 : ℂ)) x * f x = f x
  rw [Set.indicator_of_mem hx, one_mul]

theorem clopenCutoff_apply_of_notMem {V : Set X} (hV : IsClopen V) (f : SchwartzBruhat X)
    {x : X} (hx : x ∉ V) : clopenCutoff hV f x = 0 := by
  change V.indicator (fun _ => (1 : ℂ)) x * f x = 0
  rw [Set.indicator_of_notMem hx, zero_mul]

/-- Local-to-global vanishing for an algebraic distribution: if every point where `f` is
nonzero lies in a clopen set `V` such that `τ` kills every test function whose nonzero
values lie in `V`, then `τ f = 0`. Only a finite subcover of the compact support of `f`
and finite additivity of `τ` are used. -/
theorem apply_eq_zero_of_local (τ : Distribution X) (f : SchwartzBruhat X)
    (hloc : ∀ x, f x ≠ 0 → ∃ V : Set X, IsClopen V ∧ x ∈ V ∧
      ∀ g : SchwartzBruhat X, (∀ y, g y ≠ 0 → y ∈ V) → τ g = 0) :
    τ f = 0 := by
  classical
  choose V hV hxV hτV using hloc
  obtain ⟨t, ht⟩ := (Hecke.TestFunction.isCompact_support f).elim_nhds_subcover'
    (fun x hx => V x hx) (fun x hx => (hV x hx).isOpen.mem_nhds (hxV x hx))
  suffices key : ∀ (s : Finset (Function.support (f : X → ℂ))) (g : SchwartzBruhat X),
      (∀ y, g y ≠ 0 → y ∈ ⋃ x ∈ s, V x.1 x.2) → τ g = 0 from
    key t f fun y hy => ht hy
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro g hg
    have hg0 : g = 0 := by
      ext y
      by_contra hy
      simpa using hg y hy
    rw [hg0, map_zero]
  | @insert x s _ ih =>
    intro g hg
    have hsplit : g = clopenCutoff (hV x.1 x.2) g + (g - clopenCutoff (hV x.1 x.2) g) := by
      abel
    rw [hsplit, map_add]
    have h1 : τ (clopenCutoff (hV x.1 x.2) g) = 0 := by
      apply hτV x.1 x.2
      intro y hy
      by_contra hyV
      exact hy (clopenCutoff_apply_of_notMem (hV x.1 x.2) g hyV)
    have h2 : τ (g - clopenCutoff (hV x.1 x.2) g) = 0 := by
      apply ih
      intro y hy
      have hyV : y ∉ V x.1 x.2 := by
        intro hyV
        apply hy
        change g y - clopenCutoff (hV x.1 x.2) g y = 0
        rw [clopenCutoff_apply_of_mem (hV x.1 x.2) g hyV, sub_self]
      have hgy : g y ≠ 0 := by
        intro hgy
        apply hy
        change g y - clopenCutoff (hV x.1 x.2) g y = 0
        rw [clopenCutoff_apply_of_notMem (hV x.1 x.2) g hyV, hgy, sub_zero]
      have hmem := hg y hgy
      simp only [Set.mem_iUnion, Finset.mem_insert] at hmem ⊢
      obtain ⟨x', hx', hyx'⟩ := hmem
      rcases hx' with rfl | hx'
      · exact absurd hyx' hyV
      · exact ⟨x', hx', hyx'⟩
    rw [h1, h2, add_zero]

end Cutoff


end BruhatCompatibleSupport

open BruhatCompatibleSupport

/-- The support statement follows from the exact covariance statement; surjectivity of
the average and local constancy of the defects are proved, not assumed. -/
theorem bruhatCompatibleSupport_of_covariance
    (hcov : BruhatFiberCharacterCovarianceStatement.{uF}) :
    BruhatCompatibleSupportStatement.{uF} := by
  intro p hp F
  let := F.canonicalNormedField
  intro n ψ w U P H M
  let := borel U
  have : BorelSpace U := ⟨rfl⟩
  intro μ _ _ _ τ hinv
  have : IsTopologicalGroup U := F.canonicalUpperUnipotentTopologicalGroup (n + 1)
  have : T2Space U := F.canonicalUpperUnipotentT2Space (n + 1)
  have : LocallyCompactSpace U := F.canonicalUpperUnipotentLocallyCompactSpace (n + 1)
  have : NonarchimedeanGroup U := F.canonicalUpperUnipotentNonarchimedean (n + 1)
  set χ := standardCharacterContinuous ψ n with hχ
  have hsurj : Function.Surjective (SchwartzBruhat.characterAverage (Y := H) χ μ) :=
    SchwartzBruhat.characterAverageSurjective U H χ μ
  -- Local vanishing where a defect is constant and different from one.
  have hlocal : ∀ (u : P) (c : ℂ), c ≠ 1 → ∀ g : SchwartzBruhat H,
      (∀ d, g d ≠ 0 → compatibilityDefect ψ n w
        (Subgroup.inclusion (permutationUnipotentPlus_le_upperUnipotent (n + 1) F.Carrier w) u)
          d = c) → τ g = 0 := by
    intro u c hc g hg
    obtain ⟨α, rfl⟩ := hsurj g
    have heq : SchwartzBruhat.characterAverage χ μ
        (Hecke.TestFunction.pullback (bruhatFiberActHomeomorph (n + 1) F.Carrier w u) α) =
          c⁻¹ • SchwartzBruhat.characterAverage χ μ α := by
      ext d
      rw [hcov p hp F n ψ w μ α u d]
      change _ = c⁻¹ * SchwartzBruhat.characterAverage χ μ α d
      by_cases hd : SchwartzBruhat.characterAverage χ μ α d = 0
      · rw [hd, mul_zero, mul_zero]
      · rw [hg d hd]
    have h := hinv u α
    rw [Distribution.characterAverageDual_apply, Distribution.characterAverageDual_apply,
      heq, map_smul, smul_eq_mul] at h
    have h' : (c⁻¹ - 1) * τ (SchwartzBruhat.characterAverage χ μ α) = 0 := by
      rw [sub_mul, h, one_mul, sub_self]
    rcases mul_eq_zero.mp h' with h0 | h0
    · exact absurd (inv_eq_one.mp (sub_eq_zero.mp h0)) hc
    · exact h0
  rw [Distribution.mem_supportedOn_iff]
  intro f hf
  apply apply_eq_zero_of_local τ f
  intro d₀ hd₀
  have hnot : d₀ ∉ compatibleTorus ψ n w := fun hmem => hd₀ (hf d₀ hmem)
  rw [mem_compatibleTorus_iff_defect] at hnot
  push Not at hnot
  obtain ⟨v, hv, hne⟩ := hnot
  let u : P := ⟨v.val,
    (mem_permutationUnipotentPlus_iff (n + 1) F.Carrier w v.val).mpr ⟨v.property, hv⟩⟩
  have hincl : Subgroup.inclusion
      (permutationUnipotentPlus_le_upperUnipotent (n + 1) F.Carrier w) u = v :=
    Subtype.ext rfl
  -- The defect of `v` is locally constant in the diagonal parameter.
  have hconj : Continuous fun d : H =>
      (⟨permutation (n + 1) F.Carrier w * Iwasawa.diagonalUnits d * v.val *
          (permutation (n + 1) F.Carrier w * Iwasawa.diagonalUnits d)⁻¹,
        monomial_conj_mem_upperUnipotent w d hv⟩ : U) := by
    have hs : Continuous fun d : H =>
        permutation (n + 1) F.Carrier w * Iwasawa.diagonalUnits d :=
      continuous_const.mul (continuous_diagonalUnits (n + 1))
    exact ((hs.mul continuous_const).mul hs.inv).subtype_mk _
  have hχlc : IsLocallyConstant fun x : U => (standardCharacter ψ n x : ℂ) :=
    RankinSelberg.isLocallyConstant_of_continuous_complex_character (standardCharacter ψ n) χ.continuous
  have hdef : compatibilityDefect ψ n w v =
      (fun z : ℂ => z / (standardCharacter ψ n v : ℂ)) ∘
        (fun x : U => (standardCharacter ψ n x : ℂ)) ∘
          fun d : H =>
            (⟨permutation (n + 1) F.Carrier w * Iwasawa.diagonalUnits d * v.val *
                (permutation (n + 1) F.Carrier w * Iwasawa.diagonalUnits d)⁻¹,
              monomial_conj_mem_upperUnipotent w d hv⟩ : U) :=
    funext fun d => compatibilityDefect_eq_div ψ n w hv d
  have hlc : IsLocallyConstant (compatibilityDefect ψ n w v) := by
    rw [hdef]
    exact (hχlc.comp_continuous hconj).comp _
  refine ⟨{d | compatibilityDefect ψ n w v d = compatibilityDefect ψ n w v d₀},
    hlc.isClopen_fiber _, rfl, fun g hg => ?_⟩
  refine hlocal u _ hne g fun d hd => ?_
  rw [hincl]
  exact hg d hd

/-- Proof of `BruhatCompatibleSupportStatement`. -/
theorem bruhatCompatibleSupport : BruhatCompatibleSupportStatement.{uF} :=
  bruhatCompatibleSupport_of_covariance bruhatFiberCharacterCovariance

end Langlands.Whittaker
