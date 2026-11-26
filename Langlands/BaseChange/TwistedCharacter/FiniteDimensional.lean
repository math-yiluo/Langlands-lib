import Langlands.BaseChange.CharacterFunction

/-! # Twisted character functions in finite dimension -/

noncomputable section

namespace Langlands.BaseChange

open HarmonicAnalysis JacquetLanglands MeasureTheory

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- In finite dimension the pointwise trace represents the twisted character and is locally
constant on the group. -/
def FiniteDimensionalTwistedCharacterStatement : Prop :=
  ∀ [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (hρ : IsAdmissible ρ) (A : Module.End ℂ V),
    IsTwistedCharacterFunction ρ hρ A (fun g => LinearMap.trace ℂ V (ρ g ∘ₗ A)) ∧
      IsLocallyConstant (fun g => LinearMap.trace ℂ V (ρ g ∘ₗ A))

theorem finiteDimensionalTwistedCharacter :
    FiniteDimensionalTwistedCharacterStatement (G := G) (V := V) := by
  intro _ ρ hρ A
  let b := Module.finBasis ℂ V
  let c (i : Fin (Module.finrank ℂ V)) (g : G) := b.coord i (ρ g (A (b i)))
  have hc (i : Fin (Module.finrank ℂ V)) : IsLocallyConstant (c i) :=
    (Hecke.orbitMap_locallyConstant ρ (hρ.1 (A (b i)))).comp (b.coord i)
  have htrace (g : G) : LinearMap.trace ℂ V (ρ g ∘ₗ A) = ∑ i, c i g := by
    rw [LinearMap.trace_eq_matrix_trace ℂ b]
    simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply,
      LinearMap.comp_apply, ← Module.Basis.coord_apply, c]
  have hloc : IsLocallyConstant (fun g => LinearMap.trace ℂ V (ρ g ∘ₗ A)) := by
    apply IsLocallyConstant.iff_eventually_eq _ |>.2
    intro g
    filter_upwards [Filter.eventually_all.mpr fun i => (hc i).eventually_eq g]
      with y hy
    simp only [htrace, hy]
  refine ⟨?_, hloc⟩
  let _ : MeasurableSpace G := borel G
  have _ : BorelSpace G := ⟨rfl⟩
  intro μ _
  refine ⟨hloc.continuous.locallyIntegrable, fun f => ?_⟩
  rw [twistedDistribution_apply, FiniteRankEnd.trace_eq_ambient]
  change LinearMap.trace ℂ V (Hecke.integratedAction μ ρ hρ.1 f ∘ₗ A) = _
  rw [LinearMap.trace_eq_matrix_trace ℂ b]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply, LinearMap.comp_apply]
  simp_rw [← Module.Basis.coord_apply, Hecke.integratedAction_dual, htrace, Finset.mul_sum]
  rw [integral_finsetSum]
  intro i _
  exact (f.continuous.mul (hc i).continuous).integrable_of_hasCompactSupport
    f.hasCompactSupport.mul_right

end Langlands.BaseChange
