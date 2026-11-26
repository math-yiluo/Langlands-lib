import Langlands.BaseChange.TwistedPseudoCoefficientFunctionalStatement
import Langlands.BaseChange.TwistedPseudoCoefficientSpectrumTwists
import Langlands.BaseChange.TwistedSingleBlock
import Langlands.LocalField.FiniteExtensionModuleTopology

/-! # Constructing the pseudo-coefficient functional from a spectral splitting -/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory HarmonicAnalysis GeneralLinear

/-- A splitting of the twisted-character spaces gives the regular functional with the
prescribed pseudo-coefficient values. -/
def TwistedPseudoCoefficientSpectralReductionStatement.{u,v,z} : Prop :=
  TwistedPseudoCoefficientSpectrumSplittingStatement.{u,v,z} →
    TwistedPseudoCoefficientFunctionalExistenceStatement.{u,v,z}

/-- Interpolate on the orbit at the given central character, extend the resulting functional,
and use the two twist-stable spaces to prove regularity. -/
theorem twistedPseudoCoefficientFunctionalExistence_of_spectrumSplitting.{u,v,z} :
    TwistedPseudoCoefficientSpectralReductionStatement.{u,v,z} := by
  classical
  intro hsplit F _ _ _ _ _ E _ _ _ _ _ σ l n hE hn
  let : Module.Finite F E := hE.1
  let : MeasurableSpace (GeneralLinear n E) := borel _
  let : BorelSpace (GeneralLinear n E) := ⟨rfl⟩
  let := generalLinear_t2Space_of_finite F E n
  let := generalLinear_locallyCompactSpace_of_finite F E n
  let := generalLinear_totallyDisconnectedSpace_of_finite F E n
  let := LocalField.FiniteExtension.valuativeRel F E
  let := LocalField.FiniteExtension.isLocalField_of_isModuleTopology F E
  let T := LocalFieldData.ofInstances E
  let θ := entrywiseAut σ n
  have hθ := exists_compact_openSubgroup_symm_mem θ (continuous_entrywiseAut σ n) l hE.pos (by
    intro g
    change (⇑(entrywiseAut σ n))^[l] g = g
    rw [entrywiseAut_iterate_eq_pow, hE.pow_eq_one, entrywiseAut_one_apply])
  let i : Fin n := ⟨0, by omega⟩
  intro W _ _ τ hτ hdisc χ hχ A μ _
  obtain ⟨f₀, hf₁, hf₀⟩ := exists_twistOrbit_test_values μ θ hθ
    (finite_unramifiedCharacter_trivialCenter E i) τ hτ hdisc.2.1 χ hχ A
  obtain ⟨J, hJ, hDisjoint, hspan⟩ := hsplit F E σ l n hE hn W τ hdisc μ
  let L := twistedOrbitSpan μ θ τ
  let N := twistedPseudoCoefficientComplementSpan σ μ τ J
  let fL : Module.Dual ℂ L :=
    { toFun := fun d => d.val f₀
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  obtain ⟨Φ, hΦ, hzero⟩ := exists_dual_agreeOn_of_disjoint L N hDisjoint fL
  have hagree (d : Distribution (GeneralLinear n E)) (hd : d ∈ L) : Φ d = d f₀ := hΦ ⟨d, hd⟩
  have hother (d : Distribution (GeneralLinear n E))
      (hd : d ∈ twistedOtherEssentiallyTemperedSpan μ θ τ) : Φ d = 0 :=
    hzero d ((le_sup_left.trans le_sup_left : twistedOtherEssentiallyTemperedSpan μ θ τ ≤ N) hd)
  have hproper (d : Distribution (GeneralLinear n E))
      (hd : d ∈ sigmaProperInducedSpan.{u,v,z} σ μ) : Φ d = 0 :=
    hzero d ((le_sup_right.trans le_sup_left : sigmaProperInducedSpan.{u,v,z} σ μ ≤ N) hd)
  have hLmap (ψ : GeneralLinear n E →* ℂˣ) (hψ : IsUnramifiedCharacter ψ)
      (hinv : ∀ g, ψ (θ g) = ψ g) :
      L.map (characterTwistDistribution ψ hψ.isOpen_ker) ≤ L :=
    characterTwistDistribution_map_twistedOrbitSpan_le μ θ ψ hψ hinv τ
  have hNmap (ψ : GeneralLinear n E →* ℂˣ) (hψ : IsUnramifiedCharacter ψ)
      (hinv : ∀ g, ψ (θ g) = ψ g) :
      N.map (characterTwistDistribution ψ hψ.isOpen_ker) ≤ N := by
    unfold N twistedPseudoCoefficientComplementSpan
    rw [Submodule.map_sup, Submodule.map_sup]
    exact sup_le_sup (sup_le_sup
      (characterTwistDistribution_map_twistedOtherEssentiallyTemperedSpan_le μ θ ψ hψ hinv τ)
      (characterTwistDistribution_map_sigmaProperInducedSpan_le σ μ i ψ hψ hinv))
      (characterTwistDistribution_map_twistedInvisibleSpan_le μ θ ψ hψ hinv J hJ)
  refine ⟨Φ, ⟨J, hJ, ?_⟩, ?_, ?_, ?_⟩
  · intro V _ _ π hπ hirr hfix Bπ
    apply hzero
    apply (le_sup_right : twistedInvisibleSpan.{v,z} μ θ J ≤ N)
    exact twistedDistribution_mem_twistedSpectrumSpan μ θ _ hπ hirr hfix Bπ
  · intro B X _ _ Ξ hΞ hΞirr BΞ
    by_cases hB : 2 ≤ B.length
    · refine ⟨∅, 0, fun ψ hψ hψσ hI => ?_⟩
      let : IsTopologicalGroup (B.Levi E) := T.leviTopologicalGroup B
      let : T2Space (B.Levi E) := T.leviT2Space B
      let : LocallyCompactSpace (B.Levi E) := T.leviLocallyCompactSpace B
      have : ∀ j : Fin B.length, TotallyDisconnectedSpace (GeneralLinear (B.size j) E) :=
        fun j => generalLinear_totallyDisconnectedSpace_of_finite F E (B.size j)
      have : TotallyDisconnectedSpace (B.Levi E) := inferInstance
      rw [Finset.sum_empty]
      exact hproper _ (twistedDistribution_mem_sigmaProperInducedSpan σ μ B hB (twist ψ Ξ)
        ((isAdmissible_twist_iff ψ Ξ hψ.isOpen_ker).mpr hΞ) ((isIrreducible_twist_iff ψ Ξ).mpr hΞirr)
        (twistTwistedIntertwiner (leviAut σ B) ψ hψσ BΞ) hI)
    · have hBne : B.length ≠ 0 := by
        intro h
        let : IsEmpty (Fin B.length) := ⟨fun j => (Nat.not_lt_zero j.val) (h ▸ j.isLt)⟩
        have hh := B.sum_eq
        rw [Finset.univ_eq_empty, Finset.sum_empty] at hh
        omega
      exact exists_oneBlock_regular_of_spectrum_split σ B (by omega) μ L N Φ f₀
        hLmap hNmap hagree hzero hspan Ξ hΞ hΞirr BΞ
  · exact (hagree _ (twistedDistribution_mem_twistedSpectrumSpan μ θ _ hτ hdisc.2.1
      (IsUnramifiedTwistOf.refl θ τ) A)).trans hf₁
  · intro V _ _ π hπ hπirr hπtemp hχπ hne Bπ
    by_cases hOrb : IsUnramifiedTwistOf θ τ π
    · have hmem : twistedDistribution μ π hπ Bπ.toLinearMap ∈ L :=
        twistedDistribution_mem_twistedSpectrumSpan μ θ _ hπ hπirr hOrb Bπ
      exact (hagree _ hmem).trans (hf₀ V π hπ hχπ hne hOrb Bπ)
    · apply hother
      apply twistedDistribution_mem_twistedSpectrumSpan μ θ _ hπ hπirr _ Bπ
      refine ⟨hOrb, 1, fun _ _ _ _ => rfl, fun _ => rfl, ?_⟩
      simpa only [twist_one] using hπtemp

end Langlands.BaseChange
