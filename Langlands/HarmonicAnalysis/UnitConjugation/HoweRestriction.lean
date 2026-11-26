import Langlands.HarmonicAnalysis.UnitConjugation.LatticeTests
import Langlands.HarmonicAnalysis.UnitConjugation.InvariantDistribution
import Langlands.HarmonicAnalysis.Distribution.Haar
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Order.Filter.AtTopBot.Finite

/-! # The cutoff argument for restrictions to lattice-invariant tests -/

noncomputable section

namespace Langlands.HarmonicAnalysis.UnitConjugation

open Set Function Filter Submodule
open Hecke.TestFunction (pullback)

private theorem exists_eq_of_eventually_eval_eq {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : Submodule ℂ (Module.Dual ℂ V)) [FiniteDimensional ℂ W]
    (a : W) (b : ℕ → W) (h : ∀ v : V, ∀ᶠ n in atTop, (b n).val v = a.val v) : ∃ n, b n = a := by
  let E (v : V) : Module.Dual ℂ W := (Module.Dual.eval ℂ V v).comp W.subtype
  obtain ⟨I, hI, _, hspan, _⟩ := Submodule.exists_finset_span_eq_linearIndepOn ℂ (range E)
  have h' (e : Module.Dual ℂ W) (he : e ∈ I) : ∀ᶠ n in atTop, e (b n) = e a := by
    obtain ⟨v, rfl⟩ := hI he
    exact h v
  obtain ⟨n, hn⟩ := ((Filter.eventually_all_finset I).2 h').exists
  refine ⟨n, Subtype.ext (LinearMap.ext fun v => ?_)⟩
  let c : Module.Dual ℂ (Module.Dual ℂ W) := Module.Dual.eval ℂ W (b n - a)
  have H : Submodule.span ℂ (I : Set (Module.Dual ℂ W)) ≤ LinearMap.ker c := by
    apply Submodule.span_le.mpr
    intro e he
    change e (b n - a) = 0
    rw [map_sub, hn e he, sub_self]
  have hv := H (show E v ∈ Submodule.span ℂ (I : Set (Module.Dual ℂ W)) from by
    rw [hspan]
    exact Submodule.subset_span ⟨v, rfl⟩)
  change E v (b n - a) = 0 at hv
  rw [map_sub] at hv
  exact sub_eq_zero.mp hv

variable {A : Type*} [Ring A] [TopologicalSpace A] [IsTopologicalRing A]
  (L : AddSubgroup A) (hLo : IsOpen (L : Set A)) (hLc : IsCompact (L : Set A))

/-- Restriction of distributions to lattice-invariant tests, as a linear map. -/
def restrictToLatticeTests : Distribution A →ₗ[ℂ] Module.Dual ℂ (latticeInvariantTests L) :=
  (latticeInvariantTests L).subtype.dualMap

/-- Invariant distributions vanishing at the coset indicators with centers in `B`. -/
def vanishingOnLatticeCosets (B : Set A) : Submodule ℂ (Distribution A) :=
  conjugationInvariant ⊓ ⨅ x : B, LinearMap.ker (Module.Dual.eval ℂ (SchwartzBruhat A)
    (latticeCosetTest L hLo hLc x.val))

@[simp]
theorem mem_vanishingOnLatticeCosets (B : Set A) (T : Distribution A) :
    T ∈ vanishingOnLatticeCosets L hLo hLc B ↔
      IsConjugationInvariant T ∧ ∀ x ∈ B, T (latticeCosetTest L hLo hLc x) = 0 := by
  change (IsConjugationInvariant T ∧ T ∈ ⨅ x : B, LinearMap.ker _) ↔ _
  rw [Submodule.mem_iInf]
  exact and_congr_right fun _ => ⟨fun h x hx => h ⟨x, hx⟩, fun h x => h x x.property⟩

/-- The cutoff proof of the Howe restriction implication, with finite-dimensionality of the
restriction space and the invariant cutoffs supplied as premises. -/
def HoweRestrictionFromCutoffsStatement (B : Set A) : Prop :=
  FiniteDimensional ℂ ((vanishingOnLatticeCosets L hLo hLc B).map (restrictToLatticeTests L)) →
  ∀ (U : ℕ → Set A), (∀ n, IsClopen (U n)) →
    (∀ n (u : Aˣ) x, x ∈ U n ↔ conjugationHomeomorph u x ∈ U n) →
    (∀ n, ∃ ω : Set A, IsCompact ω ∧ U n ⊆ closure (conjugationSaturation ω)) →
    (∀ K : Set A, IsCompact K → ∀ᶠ n in atTop, K ⊆ U n) →
    (∀ n x, x ∈ B → ∀ y ∈ Homeomorph.addLeft x '' (L : Set A), y ∈ U n ↔ x ∈ U n) →
    ∀ T ∈ vanishingOnLatticeCosets L hLo hLc B,
      ∃ (ω : Set A) (T' : Distribution A), IsCompact ω ∧ T' ∈ invariantSupportedIn ω ∧
        restrictToLatticeTests L T' = restrictToLatticeTests L T

/-- All cutoff distributions remain in the same vanishing space. Finitely many
 test evaluations then suffice to choose a single cutoff agreeing on the entire lattice space. -/
theorem howeRestrictionFromCutoffs (B : Set A) : HoweRestrictionFromCutoffsStatement L hLo hLc B := by
  classical
  intro hfin U hU hInv hSaturation hExhaust hCoset T hT
  let J := vanishingOnLatticeCosets L hLo hLc B
  let j := restrictToLatticeTests L
  let χ (n : ℕ) : LocallyConstant A ℂ := LocallyConstant.charFn ℂ (hU n)
  let T' (n : ℕ) : Distribution A := T.comp (Distribution.multiplyTest (χ n))
  obtain ⟨hTI, hTV⟩ := (mem_vanishingOnLatticeCosets L hLo hLc B T).1 hT
  have hχ (n : ℕ) (u : Aˣ) (x : A) : χ n (conjugationHomeomorph u x) = χ n x := by
    by_cases hx : x ∈ U n
    · simp only [χ, (LocallyConstant.charFn_eq_one _ _ _).2 hx,
        (LocallyConstant.charFn_eq_one _ _ _).2 ((hInv n u x).1 hx)]
    · simp only [χ, (LocallyConstant.charFn_eq_zero _ _ _).2 hx,
        (LocallyConstant.charFn_eq_zero _ _ _).2 ((hInv n u x).not.1 hx)]
  have hT'I (n : ℕ) : IsConjugationInvariant (T' n) := by
    rw [isConjugationInvariant_iff] at hTI ⊢
    intro u f
    change T (Distribution.multiplyTest (χ n) (pullback (conjugationHomeomorph u) f)) = _
    rw [show Distribution.multiplyTest (χ n) (pullback (conjugationHomeomorph u) f) =
        pullback (conjugationHomeomorph u) (Distribution.multiplyTest (χ n) f) by
      ext x
      simp only [Distribution.multiplyTest_apply, Hecke.TestFunction.pullback_apply, hχ]]
    exact hTI u _
  have hT' (n : ℕ) : T' n ∈ J := by
    refine (mem_vanishingOnLatticeCosets L hLo hLc B _).2 ⟨hT'I n, fun x hx => ?_⟩
    let f := latticeCosetTest L hLo hLc x
    have ch : Distribution.multiplyTest (χ n) f = χ n x • f := by
      apply Hecke.TestFunction.ext
      intro y
      change χ n y * f y = χ n x * f y
      by_cases hy : y ∈ Homeomorph.addLeft x '' (L : Set A)
      · rcases (hCoset n x hx y hy) with ⟨hyx, hxy⟩
        by_cases h : x ∈ U n
        · simp only [χ, (LocallyConstant.charFn_eq_one _ _ _).2 h,
            (LocallyConstant.charFn_eq_one _ _ _).2 (hxy h)]
        · simp only [χ, (LocallyConstant.charFn_eq_zero _ _ _).2 h,
            (LocallyConstant.charFn_eq_zero _ _ _).2 (fun hy' => h (hyx hy'))]
      · have hf : f y = 0 := by
          unfold f latticeCosetTest
          rw [Hecke.TestFunction.characteristic_apply, indicator_of_notMem hy]
        simp only [hf, mul_zero]
    change T (Distribution.multiplyTest (χ n) f) = 0
    rw [ch, map_smul, show T f = 0 from hTV x hx, smul_zero]
  let W := J.map j
  let : FiniteDimensional ℂ W := hfin
  let a : W := ⟨j T, ⟨T, hT, rfl⟩⟩
  let b (n : ℕ) : W := ⟨j (T' n), ⟨T' n, hT' n, rfl⟩⟩
  have hEval (f : latticeInvariantTests L) : ∀ᶠ n in atTop, (b n).val f = a.val f := by
    filter_upwards [hExhaust _ f.val.hasCompactSupport] with n hn
    change T (Distribution.multiplyTest (χ n) f.val) = T f.val
    congr 1
    apply Hecke.TestFunction.ext
    intro x
    rw [Distribution.multiplyTest_apply]
    by_cases hx : f.val x = 0
    · simp only [hx, mul_zero]
    · have hm := hn (subset_closure (show x ∈ support (f.val : A → ℂ) from hx))
      simp only [χ, (LocallyConstant.charFn_eq_one _ _ _).2 hm, one_mul]
  obtain ⟨n, hn⟩ := exists_eq_of_eventually_eval_eq (V := ↥(latticeInvariantTests L)) W a b hEval
  obtain ⟨ω, hω, hUω⟩ := hSaturation n
  refine ⟨ω, T' n, hω, (mem_invariantSupportedIn_iff ω _).2 ⟨hT'I n, ?_⟩, congrArg Subtype.val hn⟩
  intro f hf
  change T (Distribution.multiplyTest (χ n) f) = 0
  suffices h : Distribution.multiplyTest (χ n) f = 0 by rw [h, map_zero]
  apply Hecke.TestFunction.ext
  intro x
  rw [Distribution.multiplyTest_apply]
  by_cases hx : x ∈ U n
  · rw [hf x (hUω hx), mul_zero, Submodule.coe_zero, Pi.zero_apply]
  · simp only [χ, (LocallyConstant.charFn_eq_zero _ _ _).2 hx, zero_mul, Submodule.coe_zero, Pi.zero_apply]

end Langlands.HarmonicAnalysis.UnitConjugation
