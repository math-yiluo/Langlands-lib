import Langlands.BaseChange.TwistedCharacter.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Character functions of ordinary and twisted character distributions

For a locally profinite group `G` (Hausdorff, locally compact and totally disconnected), an
admissible representation `ρ` of `G` and an endomorphism `A` of its space, a function
`Θ : G → ℂ` *represents* the twisted character `φ ↦ trace(ρ(φ) ∘ A)` when, for every Haar
measure `μ` on `G` (Borel σ-algebra), `Θ` is locally integrable for `μ` and the distribution is
`φ ↦ ∫ φ Θ dμ` (Henniart–Lemaire 2011, I.5.1 and II.1.3). The same with the ordinary character
distribution defines a character function.

The lemmas: the identity twist gives the ordinary notion; at a point where `Θ` is locally
constant, its value is the Library's local character value; the property is stable under
scaling `A` and under almost-everywhere modification of `Θ`; two character functions locally
constant at the same point agree there.

No Haar measure is chosen here: every Haar measure is a quantified argument.
-/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory HarmonicAnalysis Langlands.JacquetLanglands

universe uG uV

section Definitions

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The function `Θ` represents the twisted character of `ρ` and `A`: for every Haar measure
`μ` on `G` (Borel σ-algebra), `Θ` is locally integrable for `μ` and
`trace(ρ(φ) ∘ A) = ∫ φ Θ dμ` for every test function `φ` (Henniart–Lemaire 2011, I.5.1,
printed p. 29, and II.1.3, printed p. 57). -/
def IsTwistedCharacterFunction (ρ : Representation ℂ G V) (hρ : IsAdmissible ρ)
    (A : Module.End ℂ V) (Θ : G → ℂ) : Prop :=
  letI : MeasurableSpace G := borel G
  haveI : BorelSpace G := ⟨rfl⟩
  ∀ (μ : Measure G) [μ.IsHaarMeasure], LocallyIntegrable Θ μ ∧
    ∀ φ : SchwartzBruhat G, twistedDistribution μ ρ hρ A φ = ∫ x, φ x * Θ x ∂μ

/-- The function `Θ` represents the character of `ρ`: for every Haar measure `μ` on `G`
(Borel σ-algebra), `Θ` is locally integrable for `μ` and `trace ρ(f) = ∫ f Θ dμ` for every
test function `f` (Harish-Chandra 1999, Theorem 16.3; Henniart–Lemaire 2011, II.1.3). -/
def IsCharacterFunction (ρ : Representation ℂ G V) (hρ : IsAdmissible ρ) (Θ : G → ℂ) : Prop :=
  letI : MeasurableSpace G := borel G
  haveI : BorelSpace G := ⟨rfl⟩
  ∀ (μ : Measure G) [μ.IsHaarMeasure], LocallyIntegrable Θ μ ∧
    ∀ f : SchwartzBruhat G, Character.distribution μ ρ hρ f = ∫ x, f x * Θ x ∂μ

end Definitions

section Lemmas

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ G V} {hρ : IsAdmissible ρ}

/-- For the identity twist, a twisted character function is a character function. -/
@[simp]
theorem isTwistedCharacterFunction_one_iff {Θ : G → ℂ} :
    IsTwistedCharacterFunction ρ hρ 1 Θ ↔ IsCharacterFunction ρ hρ Θ := by
  simp only [IsTwistedCharacterFunction, IsCharacterFunction, twistedDistribution_one]

/-- At a point near which a twisted character function is constant, its value is the local
twisted character value. -/
theorem IsTwistedCharacterFunction.hasTwistedCharacterValue {A : Module.End ℂ V} {Θ : G → ℂ}
    (h : IsTwistedCharacterFunction ρ hρ A Θ) {g : G} (hg : ∀ᶠ x in nhds g, Θ x = Θ g) :
    HasTwistedCharacterValue ρ hρ A g (Θ g) := by
  let _ : MeasurableSpace G := borel G
  have _ : BorelSpace G := ⟨rfl⟩
  intro μ _
  obtain ⟨U, hUc, hUo, hgU⟩ := eventually_nhds_iff.1 hg
  refine ⟨U, hUo, hgU, fun φ hφ => ?_⟩
  rw [(h μ).2 φ, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : φ x = 0
  · simp [hx]
  · simp only
    rw [hUc x (hφ hx), mul_comm]

/-- At a point near which a character function is constant, its value is the local character
value. -/
theorem IsCharacterFunction.hasCharacterValue {Θ : G → ℂ} (h : IsCharacterFunction ρ hρ Θ)
    {g : G} (hg : ∀ᶠ x in nhds g, Θ x = Θ g) : HasCharacterValue ρ hρ g (Θ g) :=
  (hasTwistedCharacterValue_one_iff ρ hρ g (Θ g)).1
    ((isTwistedCharacterFunction_one_iff.2 h).hasTwistedCharacterValue hg)

/-- Scaling the twisting endomorphism by `a` scales the twisted character function by `a`. -/
theorem IsTwistedCharacterFunction.smul {A : Module.End ℂ V} {Θ : G → ℂ}
    (h : IsTwistedCharacterFunction ρ hρ A Θ) (a : ℂ) :
    IsTwistedCharacterFunction ρ hρ (a • A) (fun x => a * Θ x) := by
  let _ : MeasurableSpace G := borel G
  have _ : BorelSpace G := ⟨rfl⟩
  intro μ _
  obtain ⟨hli, hφ⟩ := h μ
  refine ⟨hli.smul a, fun φ => ?_⟩
  rw [twistedDistribution_smul, LinearMap.smul_apply, hφ φ, smul_eq_mul,
    ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  ring

/-- A twisted character function may be modified on a set that is null for every Haar
measure. -/
theorem IsTwistedCharacterFunction.congr_ae {A : Module.End ℂ V} {Θ Θ' : G → ℂ}
    (h : IsTwistedCharacterFunction ρ hρ A Θ)
    (hΘ : letI : MeasurableSpace G := borel G
      ∀ (μ : Measure G) [μ.IsHaarMeasure], Θ =ᵐ[μ] Θ') :
    IsTwistedCharacterFunction ρ hρ A Θ' := by
  let _ : MeasurableSpace G := borel G
  have _ : BorelSpace G := ⟨rfl⟩
  intro μ _
  obtain ⟨hli, hφ⟩ := h μ
  have hae := hΘ μ
  refine ⟨hli.congr hae, fun φ => ?_⟩
  rw [hφ φ]
  exact integral_congr_ae (hae.mono fun x hx => by simp only [hx])

/-- A character function may be modified on a set that is null for every Haar measure. -/
theorem IsCharacterFunction.congr_ae {Θ Θ' : G → ℂ} (h : IsCharacterFunction ρ hρ Θ)
    (hΘ : letI : MeasurableSpace G := borel G
      ∀ (μ : Measure G) [μ.IsHaarMeasure], Θ =ᵐ[μ] Θ') :
    IsCharacterFunction ρ hρ Θ' :=
  isTwistedCharacterFunction_one_iff.1 ((isTwistedCharacterFunction_one_iff.2 h).congr_ae hΘ)

/-- Two twisted character functions of the same `ρ` and `A` that are both constant near `g`
agree at `g`. -/
theorem IsTwistedCharacterFunction.apply_eq {A : Module.End ℂ V} {Θ Θ' : G → ℂ}
    (h : IsTwistedCharacterFunction ρ hρ A Θ) (h' : IsTwistedCharacterFunction ρ hρ A Θ')
    {g : G} (hg : ∀ᶠ x in nhds g, Θ x = Θ g) (hg' : ∀ᶠ x in nhds g, Θ' x = Θ' g) :
    Θ g = Θ' g :=
  (h.hasTwistedCharacterValue hg).unique (h'.hasTwistedCharacterValue hg')

end Lemmas

end Langlands.BaseChange
