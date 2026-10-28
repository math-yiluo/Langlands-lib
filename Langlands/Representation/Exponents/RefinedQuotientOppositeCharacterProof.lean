import Langlands.Representation.Exponents.RefinedQuotientOppositeCharacterStatement
import Langlands.Representation.Parabolic.SecondAdjointnessProof

/-!
# Scalar-character occurrence in opposite Jacquet modules

The elementary reduction sends a nonzero quotient map through second adjointness,
uses scalar equivariance to obtain an eigenvector, and proves openness of the
character kernel from the smooth stabilizer of that eigenvector.
-/

noncomputable section

namespace Langlands.Exponents

open GeneralLinear Geometric

universe uF uV uW uG uH

private theorem eigenvector_open_kernel
    {G : Type uG} [Group G] [TopologicalSpace G]
    {H : Type uH} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    {V : Type uW} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (z : H →* G) (hz : Continuous z)
    (χ : H →* ℂˣ) (hρ : IsSmooth ρ) {w : V} (hw : w ≠ 0)
    (hact : ∀ a, ρ (z a) w = (χ a : ℂ) • w) :
    IsOpen (χ.ker : Set H) := by
  obtain ⟨K, hK⟩ := hρ w
  apply Subgroup.isOpen_mono (H₁ := K.toSubgroup.comap z) ?_ (K.isOpen.preimage hz)
  intro a ha
  change χ a = 1
  apply Units.ext
  apply smul_left_injective ℂ hw
  change (χ a : ℂ) • w = (1 : ℂ) • w
  rw [← hact, one_smul]
  exact hK ⟨z a, ha⟩

/-- Scalar characters of upper refined quotients occur in their opposite
normalized Jacquet modules, and have open kernel. -/
theorem refinedQuotientOppositeCharacter :
    RefinedQuotientOppositeCharacterStatement.{uF, uV, uW} := by
  have hAdj := Parabolic.normalizedSecondAdjointness.{uF, uV, uW}.2
  intro p _ F T
  let := T.topology
  intro n hn B S σ π hσ hπ hπnt χ
  let z : (Fin (B.flatten S).length → F.Carrierˣ) →* refinedLevi F.Carrier B S :=
    (flattenedLeviEquiv F.Carrier B S).toMonoidHom.comp
      ((B.flatten S).blockScalarLevi F.Carrier)
  change Classification.HasScalarCharacter σ.ρ z χ → _
  intro hχ hq
  let := hπnt
  obtain ⟨q, hq⟩ := hq
  have hq0 : q ≠ 0 := by
    intro hzero
    obtain ⟨w, hw⟩ := exists_ne (0 : π.V)
    obtain ⟨x, hx⟩ := hq w
    exact hw (hx.symm.trans (by simp [hzero]))
  refine (hAdj p F T n hn B S).elim fun E _ => ?_
  let f := E σ π hσ hπ q
  have hf : f ≠ 0 := (E σ π hσ hπ).map_ne_zero_iff.mpr hq0
  have hex : ∃ v : σ.V, f v ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (by ext v; exact h v)
  obtain ⟨v, hv⟩ := hex
  have heig : ∀ a, T.normalizedRefinedOppositeJacquet B S π.ρ (z a) (f v) =
      (χ a : ℂ) • f v := by
    intro a
    rw [← f.isIntertwining, hχ a v, map_smul]
  let := T.moduleTopology
  let : IsTopologicalRing F.Carrier :=
    IsModuleTopology.isTopologicalRing (Padic p) F.Carrier
  have hz : Continuous z :=
    (flattenedLeviEquivContinuous F.Carrier B S).continuous.comp
      (continuous_pi fun i => GeneralLinear.scalarContinuous.continuous.comp
        (continuous_apply i))
  exact ⟨eigenvector_open_kernel _ z hz χ
      (T.isSmooth_normalizedRefinedOppositeJacquet B S hπ.1) hv heig,
    isGeneralizedEigencharacter_of_eigenvector _ χ hv heig⟩

end Langlands.Exponents
