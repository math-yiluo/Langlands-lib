import Langlands.BaseChange.TwistedCharacter.Head

/-! # A nonzero leading coefficient for a twisted head character -/

noncomputable section

namespace Langlands.BaseChange

open Classification HarmonicAnalysis MeasureTheory

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]
  (θ : MulAut G)

/-- If the irreducible head line lies outside a subspace containing the head-kernel
traces, the trace of the representation has a nonzero scalar on that line
modulo the subspace. -/
def TwistedHeadLeadingCoefficientStatement : Prop :=
  ∀ (L : Submodule ℂ (Distribution G))
    (B : SmoothRep.{0,uG,uV} ℂ G) (hB : B.IsAdmissible) (_ : B.HasFiniteLength)
    (A : B.representation.Equiv (B.representation.comp θ.toMonoidHom))
    (π : SmoothRep.{0,uG,uV} ℂ G) (hπ : π.IsAdmissible)
    (_ : IsIrreducibleHead B.representation π.representation)
    (Aπ : π.representation.Equiv (π.representation.comp θ.toMonoidHom)),
    twistedDistribution μ π.representation hπ Aπ.toLinearMap ∉ L →
    (∀ (D : SmoothRep.{0,uG,uV} ℂ G) (hD : D.IsAdmissible), D.IsIrreducible →
      SmoothRep.IsSubquotient D (B.subrepresentation (headKernel B.representation)) →
      ∀ AD : D.representation.Equiv (D.representation.comp θ.toMonoidHom),
        twistedDistribution μ D.representation hD AD.toLinearMap ∈ L) →
    ∃ a : ℂ, a ≠ 0 ∧ twistedDistribution μ B.representation hB A.toLinearMap -
      a • twistedDistribution μ π.representation hπ Aπ.toLinearMap ∈ L

/-- Adjoin the whole trace to the subspace and solve for its coefficient on the head. -/
theorem twistedDistribution_sub_smul_head_mem :
    TwistedHeadLeadingCoefficientStatement.{uG,uV} μ θ := by
  intro L B hB hBfin A π hπ hHead Aπ hOutside hLower
  let dB := twistedDistribution μ B.representation hB A.toLinearMap
  let dπ := twistedDistribution μ π.representation hπ Aπ.toLinearMap
  let L' := L ⊔ (ℂ ∙ dB)
  have hMem : dπ ∈ L' :=
    twistedDistribution_mem_of_irreducibleHead μ θ L' B hB hBfin A
      ((le_sup_right : ℂ ∙ dB ≤ L') (Submodule.mem_span_singleton_self dB)) π hπ hHead Aπ
      (fun D hD hirr hsub AD => (le_sup_left : L ≤ L') (hLower D hD hirr hsub AD))
  obtain ⟨b, hb, w, hw, hwπ⟩ := Submodule.mem_sup.mp hMem
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
  have hc : c ≠ 0 := by
    intro hc
    rw [hc, zero_smul, add_zero] at hwπ
    change dπ ∉ L at hOutside
    exact hOutside (hwπ ▸ hb)
  refine ⟨c⁻¹, inv_ne_zero hc, ?_⟩
  change dB - c⁻¹ • dπ ∈ L
  rw [← hwπ, smul_add, smul_smul, inv_mul_cancel₀ hc, one_smul, sub_add_cancel_right]
  exact L.neg_mem (L.smul_mem c⁻¹ hb)

end Langlands.BaseChange
