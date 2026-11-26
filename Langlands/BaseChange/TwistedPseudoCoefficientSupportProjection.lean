import Langlands.BaseChange.TwistedCharacter.SpectrumLines
import Langlands.BaseChange.TwistedPseudoCoefficientOrbitSeparation

/-! # Adding compact-level invisibility to separation by proper induction -/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory HarmonicAnalysis GeneralLinear

universe u v z

variable {F : Type u} [CommRing F] [TopologicalSpace F]
  {E : Type v} [Field E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
  [IsModuleTopology F E] {n : ℕ} (σ : E ≃ₐ[F] E)
  [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]
  [T2Space (GeneralLinear n E)] [LocallyCompactSpace (GeneralLinear n E)]
  [TotallyDisconnectedSpace (GeneralLinear n E)]
  (μ : Measure (GeneralLinear n E)) [μ.IsHaarMeasure]
  {V : Type z} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (GeneralLinear n E) V)

local notation "G" => GeneralLinear n E
local notation "θ" => entrywiseAut σ n

/-- Suppose a spectral condition selects the orbit and that all its representations have
nonzero fixed vectors at `J`. If each proper induction is supported entirely on one side
of this condition, separation from other essentially tempered characters and proper
inductions gives separation also after adjoining the `J`-invisible span. -/
def TwistedPseudoCoefficientSupportProjectionStatement : Prop :=
  ∀ (_ : ∀ U : OpenSubgroup G,
      ∃ K : OpenSubgroup G, K ≤ U ∧ IsCompact (K : Set G) ∧ ∀ k ∈ K, (θ).symm k ∈ K)
    (S : ∀ (W : Type z) [AddCommGroup W] [Module ℂ W], Representation ℂ G W → Prop)
    (_ : ∀ {W W' : Type z} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
      {π : Representation ℂ G W} {π' : Representation ℂ G W'},
        π.Equiv π' → S W π → S W' π')
    (J : OpenSubgroup G)
    (_ : ∀ (W : Type z) [AddCommGroup W] [Module ℂ W] (π : Representation ℂ G W),
      π.IsIrreducible → IsUnramifiedTwistOf θ τ π → S W π)
    (_ : ∀ (W : Type z) [AddCommGroup W] [Module ℂ W] (π : Representation ℂ G W),
      π.IsIrreducible → S W π → fixedVectors π J.toSubgroup ≠ ⊥)
    (_ : ∀ (B : BlockShape n), 2 ≤ B.length →
      ∀ (W : Type z) [AddCommGroup W] [Module ℂ W] (Ξ : Representation ℂ (B.Levi E) W),
        IsAdmissible Ξ → Ξ.IsIrreducible →
        ∀ (A : Ξ.Equiv (Ξ.comp (leviAut σ B).toMonoidHom))
          (h : IsAdmissible (Induction.smoothInduced (B.parabolic E) (Ξ.comp (B.leviProjection E)))),
          let d := twistedDistribution μ _ h (TwistedPaleyWiener.inducedSigmaIntertwiner σ B Ξ A).toLinearMap
          d ∈ twistedSpectrumSpan μ θ S ∨ d ∈ twistedSpectrumSpan.{v,z} μ θ (fun W _ _ π => ¬ S W π)),
    Disjoint (twistedOrbitSpan μ θ τ)
      (twistedOtherEssentiallyTemperedSpan μ θ τ ⊔ sigmaProperInducedSpan.{u,v,z} σ μ) →
    Disjoint (twistedOrbitSpan μ θ τ) (twistedPseudoCoefficientComplementSpan σ μ τ J)

/-- The projection onto the selected character lines preserves the proper-induction span
under the stated homogeneity assumption. -/
theorem disjoint_twistedOrbitSpan_complement_of_support :
    TwistedPseudoCoefficientSupportProjectionStatement σ μ τ := by
  intro hθ S hS J hOrb hJ hInd hSep
  classical
  let P := twistedSpectrumSpan μ θ S
  let Q := twistedSpectrumSpan.{v,z} μ θ (fun W _ _ π => ¬ S W π)
  obtain ⟨p, -, hp, hq⟩ := exists_twistedSpectrum_projection μ θ S
    (fun W _ _ π => ¬ S W π) hθ (fun h₁ h₂ ⟨e⟩ => h₂ (hS e h₁))
  have hL : twistedOrbitSpan μ θ τ ≤ P := by
    apply Submodule.span_mono
    rintro d ⟨W, iAdd, iMod, π, hπ, A, hirr, h, rfl⟩
    let := iAdd
    let := iMod
    exact ⟨W, iAdd, iMod, π, hπ, A, hirr, hOrb W π hirr h, rfl⟩
  have hZ : twistedInvisibleSpan.{v,z} μ θ J ≤ Q := by
    apply Submodule.span_mono
    rintro d ⟨W, iAdd, iMod, π, hπ, A, hirr, h, rfl⟩
    let := iAdd
    let := iMod
    exact ⟨W, iAdd, iMod, π, hπ, A, hirr, fun h' => hJ W π hirr h' h, rfl⟩
  let O := twistedOtherEssentiallyTemperedSpan μ θ τ
  let I := sigmaProperInducedSpan.{u,v,z} σ μ
  have hO : O ≤ O.comap p := by
    apply Submodule.span_le.mpr
    rintro d ⟨W, iAdd, iMod, π, hπ, A, hirr, h, rfl⟩
    let := iAdd
    let := iMod
    change p _ ∈ O
    by_cases hs : S W π
    · rw [hp _ (twistedDistribution_mem_twistedSpectrumSpan μ θ S hπ hirr hs A)]
      exact Submodule.subset_span ⟨W, iAdd, iMod, π, hπ, A, hirr, h, rfl⟩
    · rw [hq _ (twistedDistribution_mem_twistedSpectrumSpan μ θ (fun W _ _ π => ¬ S W π)
        hπ hirr hs A)]
      exact O.zero_mem
  have hI : I ≤ I.comap p := by
    apply Submodule.span_le.mpr
    rintro d ⟨B, hB, W, iAdd, iMod, Ξ, hΞ, hirr, A, h, rfl⟩
    let := iAdd
    let := iMod
    change p _ ∈ I
    rcases hInd B hB W Ξ hΞ hirr A h with h' | h'
    · rw [hp _ h']
      exact twistedDistribution_mem_sigmaProperInducedSpan σ μ B hB Ξ hΞ hirr A h
    · rw [hq _ h']
      exact I.zero_mem
  apply Submodule.disjoint_def.mpr
  intro d hd hd'
  obtain ⟨x, hx, y, hy, hadd⟩ := Submodule.mem_sup.mp hd'
  have hx' : p x ∈ O ⊔ I := (sup_le (hO.trans (Submodule.comap_mono le_sup_left))
    (hI.trans (Submodule.comap_mono le_sup_right))) hx
  have he : p d = p x := by rw [← hadd, map_add, hq _ (hZ hy), add_zero]
  rw [hp _ (hL hd)] at he
  exact Submodule.disjoint_def.mp hSep d hd (he.symm ▸ hx')

end Langlands.BaseChange
