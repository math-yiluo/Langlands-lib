import Langlands.Geometry.Analytic.StrictTestDomain.RationalPullbackProof
import Langlands.Geometry.Analytic.StrictTestDomain.CalculusProof
import Langlands.Geometry.Analytic.RationalLocalization

/-! # Restricting a strict-test representation to a rational domain -/

noncomputable section

universe u

namespace Langlands.Analytic.StrictTestDomain

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

namespace RationalData

variable [CompleteSpace K] {P Q : PresentedStrictAffinoidAlgebra K}

/-- Restriction to the base is injective on the spectrum of a rational quotient. -/
theorem comap_baseMap_injective (d : RationalData K P) :
    Function.Injective (BanachSpectrum.comap d.baseMap.toBoundedRingHom) :=
  RationalLocalization.comap_baseMap_injective K P d.arity d.denominator d.numerator
    d.generatesUnitIdeal

/-- The image of restriction to the base is exactly the rational locus. -/
theorem range_comap_baseMap (d : RationalData K P) :
    Set.range (BanachSpectrum.comap d.baseMap.toBoundedRingHom) = d.locus :=
  (rationalRepresentation K P d).2.1

theorem isClosed_locus (d : RationalData K P) : IsClosed d.locus :=
  (rationalRepresentation K P d).1

/-- If `i : P → Q` represents `U`, then the comparison map from the rational
quotient of `P` to the pulled-back rational quotient of `Q` represents the
inverse image of `U` in the spectrum of the rational quotient. -/
theorem represents_comparison (d : RationalData K P) {i : BoundedAlgHom K P Q}
    {U : Set (BanachSpectrum P)} (hU : Represents K i U) :
    Represents K (d.comparison i)
      (BanachSpectrum.comap d.baseMap.toBoundedRingHom ⁻¹' U) := by
  have hcomp : ∀ z : BanachSpectrum (d.pullback i).algebra,
      BanachSpectrum.comap d.baseMap.toBoundedRingHom
          (BanachSpectrum.comap (d.comparison i).toBoundedRingHom z) =
        BanachSpectrum.comap i.toBoundedRingHom
          (BanachSpectrum.comap (d.pullback i).baseMap.toBoundedRingHom z) := by
    intro z
    rw [← comap_comp_apply, ← comap_comp_apply, d.comparison_comp_baseMap i]
  have hW : Represents K ((d.pullback i).baseMap.comp i) (U ∩ d.locus) :=
    represents_comp_inter P Q _ i _ U d.locus d.isClosed_locus hU
      (d.pullback_represents i)
  refine ⟨hU.1.preimage
    (BanachSpectrum.comapContinuous d.baseMap.toBoundedRingHom).continuous, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨z, rfl⟩
      change BanachSpectrum.comap d.baseMap.toBoundedRingHom
        (BanachSpectrum.comap (d.comparison i).toBoundedRingHom z) ∈ U
      rw [hcomp]
      exact hU.hasImageIn _
    · intro hx
      have hmem : BanachSpectrum.comap d.baseMap.toBoundedRingHom x ∈ U ∩ d.locus :=
        ⟨hx, d.comap_baseMap_mem_locus x⟩
      rw [← hW.2.1] at hmem
      obtain ⟨z, hz⟩ := hmem
      refine ⟨z, d.comap_baseMap_injective ?_⟩
      rw [hcomp, ← hz, comap_comp_apply]
  · intro R φ hφ
    have hφ' : HasImageIn K (φ.comp d.baseMap) (U ∩ d.locus) := by
      intro x
      rw [comap_comp_apply]
      exact ⟨hφ x, d.comap_baseMap_mem_locus _⟩
    obtain ⟨ψ, hψ, huniq⟩ := hW.2.2 R (φ.comp d.baseMap) hφ'
    refine ⟨ψ, ?_, ?_⟩
    · apply d.hom_ext
      rw [BoundedAlgHom.comp_assoc, d.comparison_comp_baseMap i]
      exact hψ
    · intro ψ' hψ'
      apply huniq
      rw [← d.comparison_comp_baseMap i, ← BoundedAlgHom.comp_assoc, hψ']

end RationalData

end Langlands.Analytic.StrictTestDomain
