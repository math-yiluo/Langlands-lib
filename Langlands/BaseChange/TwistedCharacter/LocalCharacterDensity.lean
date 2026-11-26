import Langlands.BaseChange.CharacterFunction
import Langlands.HarmonicAnalysis.Distribution.LocallyIntegrableGluing
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # Local ordinary character densities and conjugacy -/

noncomputable section

namespace Langlands.BaseChange

open Function Filter MeasureTheory HarmonicAnalysis
open scoped NNReal Topology

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ G V} {hρ : IsAdmissible ρ}

/-- A character density on a neighborhood, for every left Haar measure. -/
def IsCharacterDensityOn (ρ : Representation ℂ G V) (hρ : IsAdmissible ρ)
    (Θ : G → ℂ) (U : Set G) : Prop :=
  letI : MeasurableSpace G := borel G
  haveI : BorelSpace G := ⟨rfl⟩
  ∀ (μ : Measure G) [μ.IsHaarMeasure], LocallyIntegrableOn Θ U μ ∧
    ∀ f : SchwartzBruhat G, support (f : G → ℂ) ⊆ U →
      Character.distribution μ ρ hρ f = ∫ x, f x * Θ x ∂μ

private def conjugationMulHomeomorph (a : G) : G ≃ₜ* G where
  toMulEquiv := MulAut.conj a
  continuous_toFun := (Distribution.conjugationHomeomorph a).continuous
  continuous_invFun := by
    change Continuous ⇑((MulAut.conj a)⁻¹)
    rw [← map_inv]
    exact (Distribution.conjugationHomeomorph a⁻¹).continuous

section Haar

variable [MeasurableSpace G] [BorelSpace G]
variable (μ : Measure G) [μ.IsHaarMeasure]

private theorem character_distribution_map_conjugation (a : G) (f : SchwartzBruhat G) :
    Character.distribution (μ.map (conjugationMulHomeomorph a)) ρ hρ
        (Hecke.TestFunction.pullback (conjugationMulHomeomorph a).toHomeomorph.symm f) =
      Character.distribution μ ρ hρ f := by
  let e := conjugationMulHomeomorph a
  let ν := μ.map e
  have : ν.IsHaarMeasure := e.isHaarMeasure_map μ
  let k := Hecke.TestFunction.pullback e.toHomeomorph.symm f
  let A : V ≃ₗ[ℂ] V :=
    { ρ a with
      invFun := ρ a⁻¹
      left_inv := ρ.inv_self_apply a
      right_inv := ρ.self_inv_apply a }
  have hact : Character.finiteRankIntegratedAction ν ρ hρ k =
      FiniteRankEnd.conjugate A (Character.finiteRankIntegratedAction μ ρ hρ f) := by
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    change Hecke.integratedAction ν ρ hρ.1 k v = ρ a (Hecke.integratedAction μ ρ hρ.1 f (ρ a⁻¹ v))
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro L
    rw [map_sub, sub_eq_zero]
    change L (Hecke.integratedAction ν ρ hρ.1 k v) =
      (L.comp (ρ a)) (Hecke.integratedAction μ ρ hρ.1 f (ρ a⁻¹ v))
    rw [Hecke.integratedAction_dual, Hecke.integratedAction_dual]
    change (∫ g, k g * L (ρ g v) ∂μ.map e.toHomeomorph.toMeasurableEquiv) = _
    rw [e.toHomeomorph.toMeasurableEquiv.measurableEmbedding.integral_map]
    have hk (g : G) : k (e g) = f g := congrArg f (e.symm_apply_apply g)
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    change k (e g) * L (ρ (a * g * a⁻¹) v) = f g * L (ρ a (ρ g (ρ a⁻¹ v)))
    rw [hk]
    simp [map_mul, Module.End.mul_apply]
  change Character.distribution ν ρ hρ k = _
  rw [Character.distribution_apply, hact, FiniteRankEnd.trace_conjugate,
    Character.distribution_apply]

end Haar

/-- Pull a local density back along conjugation. Its scalar values require no Haar factor. -/
theorem IsCharacterDensityOn.conjugate {Θ : G → ℂ} {U : Set G} (hΘ : IsCharacterDensityOn ρ hρ Θ U)
    (hU : IsOpen U) (a : G) :
    IsCharacterDensityOn ρ hρ (Θ ∘ Distribution.conjugationHomeomorph a)
      (Distribution.conjugationHomeomorph a ⁻¹' U) := by
  let _ : MeasurableSpace G := borel G
  have _ : BorelSpace G := ⟨rfl⟩
  let e := conjugationMulHomeomorph a
  change IsCharacterDensityOn ρ hρ (Θ ∘ e) (e ⁻¹' U)
  intro μ _
  let ν := μ.map e
  have : ν.IsHaarMeasure := e.isHaarMeasure_map μ
  obtain ⟨hli, htr⟩ := hΘ ν
  refine ⟨?_, fun f hf => ?_⟩
  · intro x hx
    have hxU : e x ∈ U := hx
    have hp : IsOpen (e ⁻¹' U) := hU.preimage e.continuous
    have hs := hli (e x) hxU
    rw [hU.nhdsWithin_eq hxU] at hs
    obtain ⟨s, hs, hint⟩ := hs
    rw [hp.nhdsWithin_eq hx]
    refine ⟨e ⁻¹' s, e.continuous.continuousAt.preimage_mem_nhds hs, ?_⟩
    exact e.toHomeomorph.toMeasurableEquiv.measurableEmbedding.integrableOn_map_iff.mp hint
  · let k := Hecke.TestFunction.pullback e.toHomeomorph.symm f
    have hk : support (k : G → ℂ) ⊆ U := by
      intro x hx
      have hx' : e.symm x ∈ support (f : G → ℂ) := hx
      have hm : e (e.symm x) ∈ U := hf hx'
      simpa using hm
    calc
      Character.distribution μ ρ hρ f = Character.distribution ν ρ hρ k :=
        (character_distribution_map_conjugation μ a f).symm
      _ = ∫ x, k x * Θ x ∂ν := htr k hk
      _ = ∫ x, f x * (Θ ∘ e) x ∂μ := by
        change (∫ x, k x * Θ x ∂μ.map e.toHomeomorph.toMeasurableEquiv) = _
        rw [e.toHomeomorph.toMeasurableEquiv.measurableEmbedding.integral_map]
        have hk' (g : G) : k (e g) = f g := congrArg f (e.symm_apply_apply g)
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        exact congrArg (· * Θ (e x)) (hk' x)

variable [SecondCountableTopology G]

/-- On a second-countable group, the local density identity for one Haar measure gives it
for every Haar measure. -/
theorem isCharacterDensityOn_of_oneHaar {Θ : G → ℂ} {U : Set G} :
    letI : MeasurableSpace G := borel G
    haveI : BorelSpace G := ⟨rfl⟩
    ∀ (μ : Measure G) [μ.IsHaarMeasure], LocallyIntegrableOn Θ U μ →
      (∀ f : SchwartzBruhat G, support (f : G → ℂ) ⊆ U →
        Character.distribution μ ρ hρ f = ∫ x, f x * Θ x ∂μ) →
      IsCharacterDensityOn ρ hρ Θ U := by
  let _ : MeasurableSpace G := borel G
  have _ : BorelSpace G := ⟨rfl⟩
  intro μ _ hli htr ν _
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, ν = c • μ :=
    ⟨Measure.haarScalarFactor ν μ, Measure.isMulLeftInvariant_eq_smul ν μ⟩
  subst ν
  refine ⟨?_, fun f hf => ?_⟩
  · intro x hx
    obtain ⟨s, hs, hint⟩ := hli x hx
    refine ⟨s, hs, ?_⟩
    rw [IntegrableOn, Measure.restrict_smul]
    exact hint.smul_measure_nnreal
  · have hact : Character.finiteRankIntegratedAction (c • μ) ρ hρ f =
        ((c : ℝ) : ℂ) • Character.finiteRankIntegratedAction μ ρ hρ f := by
      apply Subtype.ext
      apply LinearMap.ext
      intro v
      change Hecke.integratedAction (c • μ) ρ hρ.1 f v =
        ((c : ℝ) : ℂ) • Hecke.integratedAction μ ρ hρ.1 f v
      rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
      intro L
      rw [map_sub, sub_eq_zero, map_smul, Hecke.integratedAction_dual,
        Hecke.integratedAction_dual, integral_smul_nnreal_measure, NNReal.smul_def,
        Complex.real_smul, smul_eq_mul]
    rw [Character.distribution_apply, hact, map_smul, ← Character.distribution_apply,
      htr f hf, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul, smul_eq_mul]

/-- The semisimple-neighborhood step in character integrability. A collection of local
character densities on a set meeting every conjugacy-orbit closure gives a global density.
The subset on which the densities are locally constant is conjugation invariant. -/
theorem exists_characterFunction_of_conjugacyClosure (S R : Set G)
    (hR : ∀ a x : G, x ∈ R → a * x * a⁻¹ ∈ R)
    (hclosure : ∀ x : G,
      ∃ y ∈ closure (Set.range fun a : G => a * x * a⁻¹), y ∈ S)
    (hlocal : ∀ y ∈ S, ∃ U : Set G, IsOpen U ∧ y ∈ U ∧ ∃ Θ : G → ℂ,
      IsCharacterDensityOn ρ hρ Θ U ∧
      ∀ z ∈ U ∩ R, ∀ᶠ w in 𝓝 z, Θ w = Θ z) :
    ∃ Θ : G → ℂ, IsCharacterFunction ρ hρ Θ ∧
      ∀ x ∈ R, ∀ᶠ z in 𝓝 x, Θ z = Θ x := by
  let _ : MeasurableSpace G := borel G
  have _ : BorelSpace G := ⟨rfl⟩
  let ι := {μ : Measure G // μ.IsHaarMeasure}
  let D (μ : ι) : Distribution G :=
    have := μ.2
    Character.distribution μ.1 ρ hρ
  obtain ⟨Θ, hΘ, hloc⟩ := Distribution.exists_locallyIntegrableDensity_of_locally
    G (fun μ : ι => μ.val) D R (by
      intro x
      obtain ⟨y, hy, hyS⟩ := hclosure x
      obtain ⟨U, hU, hyU, θ, hθ, hreg⟩ := hlocal y hyS
      obtain ⟨z, hz, ⟨a, rfl⟩⟩ := mem_closure_iff.mp hy U hU hyU
      let e := Distribution.conjugationHomeomorph a
      refine ⟨e ⁻¹' U, hU.preimage e.continuous, hz, θ ∘ e, ?_, ?_⟩
      · intro μ
        have := μ.2
        exact hθ.conjugate hU a μ.1
      · intro z hz
        have hzR : e z ∈ R := hR a z hz.2
        exact (e.continuous.tendsto z).eventually (hreg (e z) ⟨hz.1, hzR⟩))
  refine ⟨Θ, fun μ hμ => ?_, hloc⟩
  exact hΘ ⟨μ, hμ⟩

end Langlands.BaseChange
