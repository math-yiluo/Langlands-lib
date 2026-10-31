import Langlands.HarmonicAnalysis.CompactCosetExpansion
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Schwartz–Bruhat functions on products

A Schwartz–Bruhat function on `X × Y` is a finite sum of products of
Schwartz–Bruhat functions on the factors, its slices are Schwartz–Bruhat, its
partial integrals are Schwartz–Bruhat, and composition with a continuous map
admitting a continuous left inverse preserves the Schwartz–Bruhat property.
-/

noncomputable section

open MeasureTheory Filter Topology

namespace Langlands.HarmonicAnalysis

universe uX uY

variable {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y]

namespace SchwartzBruhat

/-- The external product `(x, y) ↦ α x * β y` of Schwartz–Bruhat functions. -/
def tensor (α : SchwartzBruhat X) (β : SchwartzBruhat Y) : SchwartzBruhat (X × Y) :=
  ⟨fun z => α z.1 * β z.2,
    (α.locallyConstant.comp_continuous continuous_fst).comp₂
      (β.locallyConstant.comp_continuous continuous_snd) (· * ·),
    by
      apply IsCompact.of_isClosed_subset (α.hasCompactSupport.prod β.hasCompactSupport)
        (isClosed_tsupport _)
      apply closure_minimal _ ((isClosed_tsupport _).prod (isClosed_tsupport _))
      intro z hz
      have hz' : α z.1 * β z.2 ≠ 0 := hz
      exact ⟨subset_tsupport _ (left_ne_zero_of_mul hz'),
        subset_tsupport _ (right_ne_zero_of_mul hz')⟩⟩

@[simp] theorem tensor_apply (α : SchwartzBruhat X) (β : SchwartzBruhat Y) (x : X) (y : Y) :
    tensor α β (x, y) = α x * β y := rfl

/-- A Schwartz–Bruhat function composed with a continuous map that has a
continuous left inverse is Schwartz–Bruhat. -/
def compLeftInverse [T2Space Y] (f : SchwartzBruhat X) (g : Y → X) (π : X → Y)
    (hg : Continuous g) (hπ : Continuous π) (hπg : ∀ y, π (g y) = y) : SchwartzBruhat Y :=
  ⟨fun y => f (g y), f.locallyConstant.comp_continuous hg, by
    apply IsCompact.of_isClosed_subset (f.hasCompactSupport.image hπ) (isClosed_tsupport _)
    apply closure_minimal _ (f.hasCompactSupport.image hπ).isClosed
    intro y hy
    exact ⟨g y, subset_tsupport _ hy, hπg y⟩⟩

@[simp] theorem compLeftInverse_apply [T2Space Y] (f : SchwartzBruhat X) (g : Y → X) (π : X → Y)
    (hg : Continuous g) (hπ : Continuous π) (hπg : ∀ y, π (g y) = y) (y : Y) :
    compLeftInverse f g π hg hπ hπg y = f (g y) := rfl

/-- The slice `y ↦ f (x, y)` of a Schwartz–Bruhat function at a fixed first coordinate. -/
def sliceSnd [T2Space Y] (f : SchwartzBruhat (X × Y)) (x : X) : SchwartzBruhat Y :=
  compLeftInverse f (fun y => (x, y)) Prod.snd (continuous_const.prodMk continuous_id)
    continuous_snd (fun _ => rfl)

@[simp] theorem sliceSnd_apply [T2Space Y] (f : SchwartzBruhat (X × Y)) (x : X) (y : Y) :
    sliceSnd f x y = f (x, y) := rfl

/-- The curried family of slices is locally constant as a function-valued map. -/
theorem isLocallyConstant_curry (f : SchwartzBruhat (X × Y)) :
    IsLocallyConstant fun x : X => fun y : Y => f (x, y) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hK : IsCompact (Prod.snd '' tsupport (f : X × Y → ℂ)) :=
    f.hasCompactSupport.image continuous_snd
  have hev : ∀ᶠ x' in 𝓝 x, ∀ y ∈ Prod.snd '' tsupport (f : X × Y → ℂ), f (x', y) = f (x, y) := by
    apply hK.eventually_forall_of_forall_eventually
    intro y _
    have h1 : ∀ᶠ z in 𝓝 (x, y), f z = f (x, y) := f.locallyConstant.eventually_eq (x, y)
    have h2 : ∀ᶠ z in 𝓝 (x, y), f (x, z.2) = f (x, y) := by
      have ht : Tendsto (fun z : X × Y => (x, z.2)) (𝓝 (x, y)) (𝓝 (x, y)) :=
        (continuous_const.prodMk continuous_snd).tendsto' _ _ rfl
      exact ht.eventually (f.locallyConstant.eventually_eq (x, y))
    filter_upwards [h1, h2] with z hz1 hz2
    exact hz1.trans hz2.symm
  filter_upwards [hev] with x' hx'
  funext y
  by_cases hy : y ∈ Prod.snd '' tsupport (f : X × Y → ℂ)
  · exact hx' y hy
  · have h0 : ∀ x'' : X, f (x'', y) = 0 := by
      intro x''
      by_contra hne
      exact hy ⟨(x'', y), subset_tsupport _ hne, rfl⟩
    rw [h0, h0]

/-- The curried family of slices has compact support. -/
theorem hasCompactSupport_curry [T2Space X] (f : SchwartzBruhat (X × Y)) :
    HasCompactSupport fun x : X => fun y : Y => f (x, y) := by
  have hK : IsCompact (Prod.fst '' tsupport (f : X × Y → ℂ)) :=
    f.hasCompactSupport.image continuous_fst
  apply IsCompact.of_isClosed_subset hK (isClosed_tsupport _)
  apply closure_minimal _ hK.isClosed
  intro x hx
  have hx' : (fun y : Y => f (x, y)) ≠ 0 := hx
  obtain ⟨y, hy⟩ := Function.ne_iff.mp hx'
  exact ⟨(x, y), subset_tsupport _ hy, rfl⟩

/-- **Finite tensor decomposition.** Every Schwartz–Bruhat function on `X × Y` is a
finite sum of products of Schwartz–Bruhat functions on the factors. -/
theorem exists_tensor_expansion [T2Space X] [T2Space Y] (f : SchwartzBruhat (X × Y)) :
    ∃ (N : ℕ) (α : Fin N → SchwartzBruhat X) (β : Fin N → SchwartzBruhat Y),
      ∀ x y, f (x, y) = ∑ j, α j x * β j y := by
  obtain ⟨N, φ, r, hr⟩ := exists_finite_schwartz_expansion (fun x : X => fun y : Y => f (x, y))
    (isLocallyConstant_curry f) (hasCompactSupport_curry f)
  exact ⟨N, φ, fun j => sliceSnd f (r j), fun x y => hr y x⟩

/-- Schwartz–Bruhat functions are integrable for measures finite on compact sets. -/
theorem integrable [MeasurableSpace X] [OpensMeasurableSpace X] (f : SchwartzBruhat X)
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] : Integrable (f : X → ℂ) μ :=
  f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport

/-- The partial integral `x ↦ ∫ y, f (x, y) dν` of a Schwartz–Bruhat function. -/
def partialIntegral [T2Space X] [T2Space Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    (f : SchwartzBruhat (X × Y)) (ν : Measure Y) [IsFiniteMeasureOnCompacts ν] :
    SchwartzBruhat X :=
  ⟨fun x => ∫ y, f (x, y) ∂ν, by
    obtain ⟨N, α, β, hf⟩ := exists_tensor_expansion f
    have he : (fun x => ∫ y, f (x, y) ∂ν) = ∑ j, (∫ y, β j y ∂ν) • (α j : X → ℂ) := by
      funext x
      simp only [hf, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [integral_finsetSum _ (fun j _ => ((β j).integrable ν).const_mul (α j x))]
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_const_mul, mul_comm]
    rw [he]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (α j).2⟩

@[simp] theorem partialIntegral_apply [T2Space X] [T2Space Y] [MeasurableSpace Y]
    [OpensMeasurableSpace Y] (f : SchwartzBruhat (X × Y)) (ν : Measure Y)
    [IsFiniteMeasureOnCompacts ν] (x : X) :
    partialIntegral f ν x = ∫ y, f (x, y) ∂ν := rfl

end SchwartzBruhat

end Langlands.HarmonicAnalysis
