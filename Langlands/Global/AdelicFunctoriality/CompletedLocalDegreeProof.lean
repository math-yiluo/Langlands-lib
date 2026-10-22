import Langlands.Global.AdelicFunctoriality.CompletedLocalDegreeStatement
import Langlands.Global.AdelicFunctoriality.CompletedRamification
import Langlands.Global.CompletionResidueAdic
import Langlands.LocalField.DVRDegreeProof

noncomputable section

namespace Langlands.Global.AdelicFunctoriality

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField FiniteExtension Valued

universe u v

namespace FiniteExtension

variable {K : Type u} {L : Type v} [Field K] [Field L]
  [NumberField K] [NumberField L] [Algebra K L]
  (p : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L))
  [q.asIdeal.LiesOver p.asIdeal]

/-- The canonical residue comparisons commute with the extension scalar maps. -/
theorem adicResidueEquiv_algebraMap (x : 𝓞 K ⧸ p.asIdeal) :
    CompletionResidue.adicResidueEquiv L q (algebraMap (𝓞 K ⧸ p.asIdeal)
      (𝓞 L ⧸ q.asIdeal) x) =
    algebraMap (IsLocalRing.ResidueField (p.adicCompletionIntegers K))
      (IsLocalRing.ResidueField (q.adicCompletionIntegers L))
      (CompletionResidue.adicResidueEquiv K p x) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Ideal.Quotient.algebraMap_mk_of_liesOver,
    CompletionResidue.adicResidueEquiv_mk, CompletionResidue.adicResidueEquiv_mk]
  change IsLocalRing.residue _ (algebraMap (𝓞 L) (q.adicCompletionIntegers L)
    (algebraMap (𝓞 K) (𝓞 L) x)) =
    IsLocalRing.residue _ (completionIntegersMap p q
      (algebraMap (𝓞 K) (p.adicCompletionIntegers K) x))
  congr 1
  apply Subtype.ext
  change algebraMap L (q.adicCompletion L) (algebraMap K L (x : K)) =
    completionMap p q (algebraMap K (p.adicCompletion K) (x : K))
  exact (completionMap_coe p q (x : K)).symm

/-- The completed and global inertia degrees agree, by finite residue cardinalities. -/
theorem completionIntegers_inertiaDeg :
    (IsLocalRing.maximalIdeal (q.adicCompletionIntegers L)).inertiaDeg
      (p.adicCompletionIntegers K) = q.asIdeal.inertiaDeg (𝓞 K) := by
  let R := p.adicCompletionIntegers K
  let S := q.adicCompletionIntegers L
  have hi : (IsLocalRing.maximalIdeal S).inertiaDeg R =
      Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) :=
    Ideal.inertiaDeg_eq_of_isMaximal (IsLocalRing.maximalIdeal R)
      (IsLocalRing.maximalIdeal S)
  have hc := Module.natCard_eq_pow_finrank
    (K := IsLocalRing.ResidueField R) (V := IsLocalRing.ResidueField S)
  rw [← hi] at hc
  rw [CompletionResidue.card_adicResidueField K p,
    CompletionResidue.card_adicResidueField L q] at hc
  have hp := NumberField.HeightOneSpectrum.one_lt_absNorm p
  apply pow_right_injective₀ (by omega : 0 < Ideal.absNorm p.asIdeal)
    (by omega : Ideal.absNorm p.asIdeal ≠ 1)
  exact hc.symm.trans (Ideal.absNorm_pow_inertiaDeg p.asIdeal q.asIdeal).symm

end FiniteExtension

/-- The actual global ramification-inertia product is bounded by the completed degree. -/
theorem completedLocalDegreeLowerBound : CompletedLocalDegreeLowerBound.{u, v} := by
  intro K L _ _ _ _ _ p q _
  have h := Langlands.LocalField.dvrDegreeLowerBound
    (p.adicCompletionIntegers K) (q.adicCompletionIntegers L)
    (p.adicCompletion K) (q.adicCompletion L)
  rwa [FiniteExtension.completionIntegers_ramificationIdx p q,
    FiniteExtension.completionIntegers_inertiaDeg p q] at h

end Langlands.Global.AdelicFunctoriality
