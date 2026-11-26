import Langlands.JacquetLanglands.LocalCharacter
import Langlands.HarmonicAnalysis.Distribution.RenardHaarDensityProof
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-! # Choosing a density with its prescribed local distribution values -/

noncomputable section

namespace Langlands.HarmonicAnalysis.Distribution

open Set Function Filter MeasureTheory TopologicalSpace
open Langlands.JacquetLanglands
open scoped _root_.Topology

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [TotallyDisconnectedSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]

private theorem ae_eq_of_setIntegral_compactClopen {μ : Measure X} {f g : X → ℂ}
    (hf : Integrable f μ) (hg : Integrable g μ) (h₀ : (∫ x, f x ∂μ) = ∫ x, g x ∂μ)
    (h : ∀ C : Set X, IsCompact C → IsClopen C → (∫ x in C, f x ∂μ) = ∫ x in C, g x ∂μ) :
    f =ᵐ[μ] g := by
  let B : Set (Set X) := {C | IsCompact C ∧ IsClopen C}
  have hB : IsTopologicalBasis B := isTopologicalBasis_of_isOpen_of_nhds (fun _ hc => hc.2.2)
    (fun _ _ hx hu => by
      obtain ⟨C, hCc, hC, hxC, hCU⟩ := exists_isCompact_isClopen_subset hu hx
      exact ⟨C, ⟨hCc, hC⟩, hxC, hCU⟩)
  have hπ : IsPiSystem B := fun _ hs _ ht _ => ⟨hs.1.inter_right ht.2.1, hs.2.inter ht.2⟩
  have hgen : ‹MeasurableSpace X› = MeasurableSpace.generateFrom B :=
    (BorelSpace.measurable_eq (α := X)).trans hB.borel_eq_generateFrom
  apply hf.ae_eq_of_forall_setIntegral_eq f g hg
  suffices hS : ∀ S : Set X, MeasurableSet S → (∫ x in S, f x ∂μ) = ∫ x in S, g x ∂μ by
    exact fun S hs _ => hS S hs
  intro S hS
  induction S, hS using MeasurableSpace.induction_on_inter hgen hπ with
  | empty => simp
  | basic S hS => exact h S hS.1 hS.2
  | compl S hS ih =>
    have h1 := integral_add_compl hS hf
    have h2 := integral_add_compl hS hg
    rw [ih, h₀] at h1
    exact add_left_cancel (h1.trans h2.symm)
  | iUnion S hdisj hS ih =>
    rw [integral_iUnion hS hdisj hf.integrableOn, integral_iUnion hS hdisj hg.integrableOn]
    simp_rw [ih]

/-- A locally integrable density can be chosen to equal the local distribution values on an
open set, for the whole family of measures for which the original density and values hold. -/
def RegularValuesDensityStatement {ι : Type*} (μ : ι → Measure X) (D : ι → Distribution X)
    (R : Set X) : Prop :=
  Nonempty ι → (∀ j, IsFiniteMeasureOnCompacts (μ j)) → (∀ j, (μ j).IsOpenPosMeasure) →
  IsOpen R →
  (∃ θ : X → ℂ, ∀ j, LocallyIntegrable θ (μ j) ∧
    ∀ f : SchwartzBruhat X, D j f = ∫ x, f x * θ x ∂(μ j)) →
  (∀ x ∈ R, ∃ c : ℂ, ∀ j, HasLocalValue (μ j) (D j) x c) →
  ∃ Θ : X → ℂ, (∀ j, LocallyIntegrable Θ (μ j) ∧
    ∀ f : SchwartzBruhat X, D j f = ∫ x, f x * Θ x ∂(μ j)) ∧
    ∀ x ∈ R, ∀ᶠ y in 𝓝 x, Θ y = Θ x

theorem regularValuesDensity {ι : Type*} (μ : ι → Measure X) (D : ι → Distribution X) (R : Set X) :
    RegularValuesDensityStatement μ D R := by
  classical
  rintro ⟨j₀⟩ hfin hpos hR ⟨θ, hθ⟩ hval
  choose c hc using fun x : R => hval x.val x.property
  let Θ (x : X) := if hx : x ∈ R then c ⟨x, hx⟩ else θ x
  have hΘ (x : R) : Θ x.val = c x := dite_eq_left x.property
  have hlc (x : R) : ∀ᶠ y in 𝓝 x.val, Θ y = Θ x.val := by
    obtain ⟨U, hU, hxU, hUval⟩ := hc x j₀
    filter_upwards [(hR.inter hU).mem_nhds ⟨x.property, hxU⟩] with y hy
    let z : R := ⟨y, hy.1⟩
    have hz : HasLocalValue (μ j₀) (D j₀) y (c x) := ⟨U, hU, hy.2, hUval⟩
    have := hfin j₀
    have := hpos j₀
    exact (hΘ z).trans (((hc z j₀).unique hz).trans (hΘ x).symm)
  refine ⟨Θ, fun j => ?_, fun x hx => hlc ⟨x, hx⟩⟩
  have := hfin j
  have hlocal (x : R) : ∃ K : Set X, IsClopen K ∧ x.val ∈ K ∧ K ⊆ R ∧ Θ =ᵐ[(μ j).restrict K] θ := by
    obtain ⟨U, hU, hxU, hUval⟩ := hc x j
    have hN := Filter.inter_mem (hlc x) ((hR.inter hU).mem_nhds ⟨x.property, hxU⟩)
    obtain ⟨K, hKc, hK, hxK, hsub⟩ := HarmonicAnalysis.exists_compact_clopen hN
    have hKU : K ⊆ U := fun z hz => (hsub hz).2.2
    have hKR : K ⊆ R := fun z hz => (hsub hz).2.1
    let ν := (μ j).restrict K
    have : IsFiniteMeasure ν := ⟨by
      change (μ j).restrict K univ < _
      rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
      exact hKc.measure_lt_top⟩
    have hKint : Integrable θ ν := (hθ j).1.integrableOn_isCompact hKc
    have hC (C : Set X) (hCc : IsCompact C) (hC : IsClopen C) (hCK : C ⊆ K) :
        (∫ y in C, θ y ∂(μ j)) = ∫ y in C, c x ∂(μ j) := by
      let f := Hecke.TestFunction.characteristic hC hCc
      have hf : Function.support (f : X → ℂ) ⊆ U := by
        rw [Hecke.TestFunction.support_characteristic]
        exact hCK.trans hKU
      have he := ((hθ j).2 f).symm.trans (hUval f hf)
      rw [← integral_const_mul] at he
      have hleft : (fun y => f y * θ y) = C.indicator θ := by
        funext y
        by_cases hy : y ∈ C <;> simp [f, Hecke.TestFunction.characteristic_apply, hy]
      have hright : (fun y => c x * f y) = C.indicator (fun _ => c x) := by
        funext y
        by_cases hy : y ∈ C <;> simp [f, Hecke.TestFunction.characteristic_apply, hy]
      rw [hleft, hright, integral_indicator hC.2.measurableSet, integral_indicator hC.2.measurableSet] at he
      exact he
    have hθc : θ =ᵐ[ν] fun _ => c x := by
      apply ae_eq_of_setIntegral_compactClopen hKint (integrable_const _)
      · exact hC K hKc hK subset_rfl
      · intro C hCc hCl
        change (∫ y in C, θ y ∂(μ j).restrict K) = ∫ y in C, c x ∂(μ j).restrict K
        rw [Measure.restrict_restrict hCl.2.measurableSet]
        exact hC _ (hCc.inter_right hK.1) (hCl.inter hK) inter_subset_right
    refine ⟨K, hK, hxK, hKR, ?_⟩
    filter_upwards [ae_restrict_mem hK.2.measurableSet, hθc] with z hz hz'
    exact ((hsub hz).1.trans (hΘ x)).trans hz'.symm
  choose K hK hxK hKR hKae using hlocal
  have hcover : (⋃ x : R, K x) = R := by
    ext y
    exact ⟨fun hy => by obtain ⟨x, hx⟩ := mem_iUnion.mp hy; exact hKR x hx,
      fun hy => mem_iUnion.mpr ⟨⟨y, hy⟩, hxK ⟨y, hy⟩⟩⟩
  obtain ⟨S, hSc, hS⟩ := isOpen_iUnion_countable K (fun x => (hK x).2)
  have hre : Θ =ᵐ[(μ j).restrict R] θ := by
    rw [← hcover, ← hS]
    exact (ae_eq_restrict_biUnion_iff K hSc Θ θ).2 (fun x _ => hKae x)
  have hae : Θ =ᵐ[μ j] θ := by
    rw [Filter.EventuallyEq, ae_restrict_iff' hR.measurableSet] at hre
    filter_upwards [hre] with x hx
    by_cases hxR : x ∈ R
    · exact hx hxR
    · exact dite_eq_right hxR
  refine ⟨(hθ j).1.congr hae.symm, fun f => ?_⟩
  rw [(hθ j).2 f]
  exact integral_congr_ae (hae.mono fun x h => congrArg (f x * ·) h.symm)

end Langlands.HarmonicAnalysis.Distribution
