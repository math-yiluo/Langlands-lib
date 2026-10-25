import Langlands.Representation.Whittaker.GeneralizedCoefficient
import Langlands.Representation.CompactCoefficient.AdmissibleRetraction
import Langlands.Representation.Hecke.SmoothTranspose

/-! # Range and separation for generalized coefficients -/

noncomputable section

namespace Langlands.Whittaker

open HarmonicAnalysis MeasureTheory MeasureTheory.Measure

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
variable [MeasurableSpace G] [BorelSpace G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [IsMulRightInvariant μ]
variable (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)

/-- The range of full-transpose smoothing is stable under the smooth dual action. -/
def smoothFunctionalRange (ℓ : Module.Dual ℂ V) :
    Subrepresentation (smoothContragredient ρ) where
  toSubmodule := LinearMap.range (smoothFunctional μ ρ hρ ℓ)
  apply_mem_toSubmodule a := by
    rintro _ ⟨f, rfl⟩
    exact ⟨Hecke.TestFunction.rightTranslate a f,
      smoothFunctional_rightTranslate μ ρ hρ ℓ a f⟩

@[simp]
theorem mem_smoothFunctionalRange (ℓ : Module.Dual ℂ V) (φ : SmoothDual ρ) :
    φ ∈ smoothFunctionalRange μ ρ hρ ℓ ↔
      ∃ f, smoothFunctional μ ρ hρ ℓ f = φ := Iff.rfl

omit [MeasurableSpace G] [BorelSpace G] in
private theorem compactOpenCofinal :
    ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K := by
  intro K
  obtain ⟨L, hLK, hL, _⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance G ∅ K
  exact ⟨L, hL, hLK⟩

variable [IsMulLeftInvariant μ] [IsOpenPosMeasure μ]

/-- A nonzero functional on an admissible irreducible representation smooths
onto the entire actual smooth dual. -/
theorem smoothFunctional_surjective (hAdm : IsAdmissible ρ)
    (hIrr : ρ.IsIrreducible) (ℓ : Module.Dual ℂ V) (hℓ : ℓ ≠ 0) :
    Function.Surjective (smoothFunctional μ ρ hρ ℓ) := by
  have hi := CompactSplitting.isIrreducible_smoothContragredient
    (compactOpenCofinal (G := G)) ρ hAdm hIrr
  have ht : smoothFunctionalRange μ ρ hρ ℓ = ⊤ := by
    rcases hi.eq_bot_or_eq_top (smoothFunctionalRange μ ρ hρ ℓ) with hb | ht
    · exfalso
      apply hℓ
      apply (smoothFunctional_eq_zero_iff μ ρ hρ ℓ).1
      apply LinearMap.ext
      intro f
      have hm : smoothFunctional μ ρ hρ ℓ f ∈ smoothFunctionalRange μ ρ hρ ℓ :=
        ⟨f, rfl⟩
      rw [hb] at hm
      exact (Submodule.mem_bot ℂ).1 hm
    · exact ht
  intro φ
  have hm : φ ∈ smoothFunctionalRange μ ρ hρ ℓ := by
    rw [ht]
    exact Submodule.mem_top
  exact hm

/-- The common kernel of the translates of a functional on the smooth dual. -/
def smoothDualOrbitKernel (η : Module.Dual ℂ (SmoothDual ρ)) :
    Subrepresentation (smoothContragredient ρ) where
  toSubmodule := ⨅ a : G, LinearMap.ker (η.comp (smoothContragredient ρ a))
  apply_mem_toSubmodule b := by
    intro φ hφ
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.comp_apply] at hφ ⊢
    intro a
    simpa only [map_mul, Module.End.mul_apply] using hφ (a * b)

omit [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] in
@[simp]
theorem mem_smoothDualOrbitKernel (η : Module.Dual ℂ (SmoothDual ρ))
    (φ : SmoothDual ρ) :
    φ ∈ smoothDualOrbitKernel ρ η ↔
      ∀ a : G, η (smoothContragredient ρ a φ) = 0 := by
  change (φ ∈ ⨅ a : G, LinearMap.ker (η.comp (smoothContragredient ρ a))) ↔ _
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.comp_apply]

omit [MeasurableSpace G] [BorelSpace G] in
/-- The translates of any nonzero algebraic functional separate the smooth dual. -/
theorem smoothDualOrbitKernel_eq_bot (hAdm : IsAdmissible ρ)
    (hIrr : ρ.IsIrreducible) (η : Module.Dual ℂ (SmoothDual ρ)) (hη : η ≠ 0) :
    smoothDualOrbitKernel ρ η = ⊥ := by
  have hi := CompactSplitting.isIrreducible_smoothContragredient
    (compactOpenCofinal (G := G)) ρ hAdm hIrr
  rcases hi.eq_bot_or_eq_top (smoothDualOrbitKernel ρ η) with hb | ht
  · exact hb
  · exfalso
    apply hη
    ext φ
    have hm : φ ∈ smoothDualOrbitKernel ρ η := by
      rw [ht]
      exact Submodule.mem_top
    have h := (mem_smoothDualOrbitKernel ρ η φ).1 hm (1 : G)
    simpa using h

variable [IsInvInvariant μ]

omit [IsMulLeftInvariant μ] [IsOpenPosMeasure μ] in
/-- On a smooth functional, full-transpose smoothing is the restricted transpose. -/
theorem smoothFunctional_pairing (φ : SmoothDual ρ) (f : SchwartzBruhat G) :
    smoothFunctional μ ρ hρ (smoothDualPairing ρ φ) f =
      Hecke.integratedTranspose μ ρ hρ f φ := rfl

/-- Smoothing a smooth functional by all test functions, then evaluating at one
nonzero functional on the smooth dual, detects whether it is zero. -/
theorem smoothFunctional_separates (hAdm : IsAdmissible ρ)
    (hIrr : ρ.IsIrreducible) (η : Module.Dual ℂ (SmoothDual ρ)) (hη : η ≠ 0)
    (φ : SmoothDual ρ) :
    (∀ f : SchwartzBruhat G,
      η (smoothFunctional μ ρ hρ (smoothDualPairing ρ φ) f) = 0) ↔ φ = 0 := by
  constructor
  · intro h
    let : μ.IsHaarMeasure := {}
    obtain ⟨J, hJ, hu⟩ := Hecke.exists_normalizedIndicator_fixes μ
      (smoothContragredient ρ) (isSmooth_smoothContragredient ρ) φ
    let u := Hecke.HeckeAlgebra.toTestFunction μ
      (Hecke.HeckeAlgebra.normalizedIndicator μ J hJ)
    have he : smoothFunctional μ ρ hρ (smoothDualPairing ρ φ)
        (Hecke.TestFunction.inversion u) = φ := by
      rw [smoothFunctional_pairing, Hecke.integratedTranspose_eq_integratedAction_inversion,
        Hecke.TestFunction.inversion_inversion]
      exact hu
    have hm : φ ∈ smoothDualOrbitKernel ρ η := by
      rw [mem_smoothDualOrbitKernel]
      intro a
      have ha := h (Hecke.TestFunction.rightTranslate a (Hecke.TestFunction.inversion u))
      rwa [smoothFunctional_rightTranslate, he] at ha
    rw [smoothDualOrbitKernel_eq_bot ρ hAdm hIrr η hη] at hm
    exact (Submodule.mem_bot ℂ).1 hm
  · rintro rfl f
    simp

/-- The left convolution annihilator of a generalized coefficient is exactly
its smoothing kernel when the second functional is nonzero. -/
theorem generalizedCoefficient_left_annihilator (hAdm : IsAdmissible ρ)
    (hIrr : ρ.IsIrreducible) (ℓ : Module.Dual ℂ V)
    (η : Module.Dual ℂ (SmoothDual ρ)) (hη : η ≠ 0) (f : SchwartzBruhat G) :
    (∀ g : SchwartzBruhat G,
      generalizedCoefficient μ ρ hρ ℓ η (Hecke.TestFunction.convolution μ f g) = 0) ↔
      smoothFunctional μ ρ hρ ℓ f = 0 := by
  simpa only [generalizedCoefficient_apply, smoothFunctional_convolution] using
    smoothFunctional_separates μ ρ hρ hAdm hIrr η hη (smoothFunctional μ ρ hρ ℓ f)

omit [IsInvInvariant μ] in
/-- For a nonzero first functional, the right convolution annihilator depends
only on the second functional. -/
theorem generalizedCoefficient_right_annihilator (hAdm : IsAdmissible ρ)
    (hIrr : ρ.IsIrreducible) (ℓ : Module.Dual ℂ V) (hℓ : ℓ ≠ 0)
    (η : Module.Dual ℂ (SmoothDual ρ)) (g : SchwartzBruhat G) :
    (∀ f : SchwartzBruhat G,
      generalizedCoefficient μ ρ hρ ℓ η (Hecke.TestFunction.convolution μ f g) = 0) ↔
      ∀ φ : SmoothDual ρ, η (smoothFunctional μ ρ hρ (smoothDualPairing ρ φ) g) = 0 := by
  constructor
  · intro h φ
    obtain ⟨f, rfl⟩ := smoothFunctional_surjective μ ρ hρ hAdm hIrr ℓ hℓ φ
    simpa only [generalizedCoefficient_apply, smoothFunctional_convolution] using h f
  · intro h f
    simpa only [generalizedCoefficient_apply, smoothFunctional_convolution] using
      h (smoothFunctional μ ρ hρ ℓ f)

end Langlands.Whittaker
