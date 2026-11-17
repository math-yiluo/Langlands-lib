import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CentralProjectionSquareIntegrable
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CentralQuotientHaar
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalCentralImage

/-! # The actual central projection norm on an arbitrary Haar quotient -/

noncomputable section

universe uG

open MeasureTheory TopologicalSpace Langlands.QuotientIntegration

namespace Langlands.HarishChandraSchwartz

section QuotientNorm

variable {Γ : Type uG} [Group Γ] {A : Subgroup Γ}
  [MeasurableSpace A] [MeasurableMul A]
  (hA : A ≤ Subgroup.center Γ) (muA : Measure A) [muA.IsMulRightInvariant]
  (χ : A →* ℂˣ) (hu : IsUnitaryCharacter χ)

/-- The literal norm of the central projection descends to the specified
central quotient. This uses the original central measure. -/
def centralProjectionQuotientNorm (f : Γ → ℂ) : Γ ⧸ A → ℝ :=
  Quotient.lift (fun g => ‖centralProjection muA χ f g‖) (by
    intro x y hxy
    have ha : x⁻¹ * y ∈ A := QuotientGroup.leftRel_apply.mp hxy
    let a : A := ⟨x⁻¹ * y, ha⟩
    have hc : x * (a : Γ) = (a : Γ) * x :=
      Subgroup.mem_center_iff.mp (hA a.property) x
    have he := norm_centralProjection_mul_left (μA := muA) hu f a x
    rw [← hc] at he
    simpa only [a, mul_inv_cancel_left] using he.symm)

@[simp] theorem centralProjectionQuotientNorm_mk (f : Γ → ℂ) (g : Γ) :
    centralProjectionQuotientNorm hA muA χ hu f (QuotientGroup.mk g) =
      ‖centralProjection muA χ f g‖ := rfl

end QuotientNorm

section Integrability

variable {Γ : Type uG} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [hT2 : T2Space Γ] [hLc : LocallyCompactSpace Γ] [hSc : SecondCountableTopology Γ]
  [MeasurableSpace Γ] [hBorG : BorelSpace Γ]
  [Nonempty (CompactOpenSubgroup Γ)]
  {A : Subgroup Γ} [A.Normal] (hAc : IsClosed (A : Set Γ))
  (hA : A ≤ Subgroup.center Γ)
  [MeasurableSpace A] [hBorA : BorelSpace A]
  (muA : Measure A) [hHaarA : muA.IsHaarMeasure] [hRightA : muA.IsMulRightInvariant]
  (muG : Measure Γ) [hHaarG : muG.IsHaarMeasure] [hRightG : muG.IsMulRightInvariant]
  [MeasurableSpace (Γ ⧸ A)] [BorelSpace (Γ ⧸ A)]
  (mu : Measure (Γ ⧸ A)) [mu.IsHaarMeasure]
  {Ξ σ : Γ → ℝ} (hw : CentralWeights muA Ξ σ) (hL : L2Weights muG Ξ σ)
  (χ : A →* ℂˣ) (hu : IsUnitaryCharacter χ)

include hAc hA hu muG hw hL hT2 hLc hSc hBorA hBorG hHaarA hRightA hHaarG hRightG

/-- The actual central-projection norm is square integrable for every specified
Haar measure on `Γ/A`. Quotient-measure comparison retains its finite scalar. -/
theorem centralProjectionQuotientNorm_memLp_two (f : Space Ξ σ) :
    MemLp (centralProjectionQuotientNorm hA muA χ hu (f : Γ → ℂ)) 2 mu := by
  let : MeasurableSpace (LeftQuotient A) := borel _
  have : BorelSpace (LeftQuotient A) := ⟨rfl⟩
  have : LocallyCompactSpace A := hAc.locallyCompactSpace
  have : SecondCountableTopology A := Subtype.secondCountableTopology (A : Set Γ)
  have : T2Space A := inferInstance
  have : PseudoMetrizableSpace A := inferInstance
  have : SigmaCompactSpace A := inferInstance
  have : IsLocallyFiniteMeasure muA := inferInstance
  have : SigmaFinite muA := inferInstance
  have : muA.Regular := inferInstance
  have : muG.Regular := inferInstance
  obtain ⟨nu, hnu⟩ := compatibleMeasureExists A hAc muG muA
  obtain ⟨F₀, hF₀, hF₀g⟩ := exists_memLp_two_centralProjection hAc hnu hA hw hL hu
    (Space.coe_mem f)
  obtain ⟨F, hF, hFg⟩ := hnu.exists_memLp_quotientGroup hAc hA mu hF₀
  have he : F = centralProjectionQuotientNorm hA muA χ hu (f : Γ → ℂ) := by
    funext q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    exact (hFg g).trans (hF₀g g)
  exact he ▸ hF

/-- Every element of the full raw central image has an actual square-integrable
quotient norm. This conclusion uses a raw Schwartz preimage, not a span witness. -/
theorem exists_memLp_two_of_mem_schwartzCentralIntegralImage
    (E : Submodule ℂ (Space Ξ σ)) {f : Γ → ℂ}
    (hf : f ∈ schwartzCentralIntegralImage E muA χ) :
    ∃ F : Γ ⧸ A → ℝ, MemLp F 2 mu ∧
      ∀ g : Γ, F (QuotientGroup.mk g) = ‖f g‖ := by
  obtain ⟨φ, _, hφ⟩ := hf
  refine ⟨centralProjectionQuotientNorm hA muA χ hu (φ : Γ → ℂ),
    centralProjectionQuotientNorm_memLp_two hAc hA muA muG mu hw hL χ hu φ, ?_⟩
  intro g
  rw [centralProjectionQuotientNorm_mk, hφ]

end Integrability

end Langlands.HarishChandraSchwartz
