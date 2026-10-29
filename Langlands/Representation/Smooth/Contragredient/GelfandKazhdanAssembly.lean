import Langlands.Representation.Smooth.Contragredient.GelfandKazhdanStatement
import Langlands.Representation.Character.TransportProof
import Langlands.Representation.Character.SeparationStatement
import Langlands.HarmonicAnalysis.Distribution.TransposeInvariantStatement
import Langlands.Representation.RankinSelberg.HaarSymmetriesProof
import Langlands.Representation.Classification.SupercuspidalContragredientAux
import Langlands.Representation.Smooth.Contragredient.AdmissibleDualityProof
import Langlands.Representation.CompactCoefficient.GroupTransport
import Langlands.Group.GL.CompactOpen
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected

noncomputable section

namespace Langlands

open HarmonicAnalysis MeasureTheory MeasureTheory.Measure

universe uF uV

/-- Conditional assembly: character separation and distribution transpose invariance
remain explicit; character transport and Haar symmetries use published proofs. -/
theorem gelfandKazhdanContragredient_of_character_inputs
    (hseparation : CharacterSeparationStatement.{uF,uV,uV})
    (htranspose : GeneralLinearConjugationDistributionTransposeStatement.{uF}) :
    GelfandKazhdanContragredientStatement.{uF,uV} := by
  intro p hp F
  let := hp
  let := F.canonicalNormedField
  let := F.canonicalTopologicalData.valuativeRel
  let : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
  intro n V _ _ ρ hρ hirr
  let G := Matrix.GeneralLinearGroup (Fin (n + 1)) F.Carrier
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let : LocallyCompactSpace G := F.canonicalGeneralLinearLocallyCompactSpace (n + 1)
  let : NonarchimedeanGroup G := F.canonicalGeneralLinearNonarchimedean (n + 1)
  let μ := RankinSelberg.generalLinearHaar F.Carrier n
  obtain ⟨hinv, he, _, hconj⟩ := RankinSelberg.generalLinearHaarSymmetries F.Carrier n
  let : IsInvInvariant μ := hinv
  let e := GeneralLinear.inverseTransposeContinuous (n + 1) F.Carrier
  obtain ⟨hdual, hdualChar⟩ := characterTransport.1 G μ V ρ hρ
  obtain ⟨hpull, hpullChar⟩ := characterTransport.2 G μ e he V ρ hρ
  have hcofinal : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L ≤ K := by
    intro K
    obtain ⟨L, hLK, hLc, _⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance G ∅ K
    exact ⟨L, hLc, hLK⟩
  have hdualIrr : Representation.IsIrreducible (smoothContragredient ρ) :=
    (isIrreducible_smoothContragredient_iff_of_bidual
      (fun W _ _ σ hσ => smoothBidual_injective_of_compact_cofinal hcofinal σ hσ)
      ρ hρ.1 ⟨smoothBidual_injective_of_compact_cofinal hcofinal ρ hρ.1,
        smoothBidual_surjective_of_compact_cofinal hcofinal ρ hρ⟩).mpr hirr
  have hpullIrr : Representation.IsIrreducible (ρ.comp e.toMonoidHom) :=
    (isIrreducible_comp_continuousMulEquiv_iff ρ e).mpr hirr
  have hDconj : Distribution.IsConjugationInvariant (Character.distribution μ ρ hρ) :=
    Character.distribution_isConjugationInvariant_of_measurePreserving μ ρ hρ hconj
  have hDtrans := htranspose p hp F n (Character.distribution μ ρ hρ) hDconj
  have hchars : Character.distribution μ (ρ.comp e.toMonoidHom) hpull =
      Character.distribution μ (smoothContragredient ρ) hdual := by
    ext f
    rw [hpullChar, hdualChar]
    have htest : Hecke.TestFunction.pullback e.symm.toHomeomorph f =
        Hecke.TestFunction.pullback (Distribution.transposeHomeomorph (n + 1) F.Carrier)
          (Hecke.TestFunction.inversion f) := by
      ext g
      change f (GeneralLinear.inverseTranspose (n + 1) F.Carrier g) =
        f ((GeneralLinear.inverseTranspose (n + 1) F.Carrier g⁻¹)⁻¹)
      rw [map_inv, inv_inv]
    rw [htest]
    exact (Distribution.isTransposeInvariant_iff _ _ _).mp hDtrans _
  exact (hseparation G μ V (SmoothDual ρ) (ρ.comp e.toMonoidHom)
    (smoothContragredient ρ) hpull hdual hpullIrr hdualIrr).mp hchars

end Langlands
