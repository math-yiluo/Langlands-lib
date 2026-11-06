import Langlands.Representation.Jacquet.StablePairingProof
import Langlands.Representation.Jacquet.IwahoriContractionAdmissibility
import Langlands.Representation.Jacquet.CompressionSplittingDuality
import Langlands.Representation.Smooth.Contragredient.AdmissibleDualityProof

/-! Fitting splittings of the two compressed actions, and in particular
admissibility, supply the stable-pairing hypotheses under both Iwahori
contraction orientations on the given good compact open subgroups. -/

noncomputable section

namespace Langlands.Jacquet.StablePairingData

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

variable (D : StablePairingData G) (ρ : Representation ℂ G V) (hρ : IsAdmissible ρ)
variable
  (hUpper : ∀ K, D.Good K → IsIwahoriContraction K D.N D.M D.Nbar D.g)
  (hLower : ∀ K, D.Good K → IsIwahoriContraction K D.Nbar D.M D.N D.g⁻¹)

include hUpper hLower in
/-- Both contraction orientations on the good family discharge all of `Admits`
for a smooth representation once compression by `g` on the `K`-fixed smooth
functionals and compression by `g⁻¹` on the `K`-fixed vectors have the Fitting
splitting for every good `K`. No finite dimensionality is assumed. -/
theorem admits_of_iwahoriContractions_of_splits (hs : IsSmooth ρ)
    (hUpperSplit : ∀ K (hK : D.Good K),
      CompactCompressionSplits (smoothContragredient ρ) (isSmooth_smoothContragredient ρ) K
        (D.isCompact K hK) D.g)
    (hLowerSplit : ∀ K (hK : D.Good K),
      CompactCompressionSplits ρ hs K (D.isCompact K hK) D.g⁻¹) :
    D.Admits ρ hs where
  duality K hK :=
    compactCompression_stableEvaluationDuality_of_splits ρ hs K _ _ (hLowerSplit K hK)
  upper_surjective K hK :=
    (stableImageJacquetMap_bijective_of_splits
      (smoothContragredient ρ) (isSmooth_smoothContragredient ρ)
      (D.isCompact K hK) (hUpper K hK) D.hMN (hUpperSplit K hK)).2
  upper_kernel K hK :=
    (powerKernelSup_eq_ker_of_iwahoriContraction
      (smoothContragredient ρ) (isSmooth_smoothContragredient ρ)
      (D.isCompact K hK) (hUpper K hK) D.hMN).ge
  lower_surjective K hK :=
    (stableImageJacquetMap_bijective_of_splits ρ hs
      (D.isCompact K hK) (hLower K hK) D.hMNbar (hLowerSplit K hK)).2
  lower_kernel K hK :=
    (powerKernelSup_eq_ker_of_iwahoriContraction ρ hs
      (D.isCompact K hK) (hLower K hK) D.hMNbar).ge

include hUpper hLower in
/-- Both contraction orientations on the good family discharge all of `Admits`
for an admissible representation. No representation-theoretic lift hypothesis
is required as an additional input. -/
theorem admits_of_iwahoriContractions : D.Admits ρ hρ.1 := by
  have hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L ≤ K := by
    intro K
    obtain ⟨L, hL, hLK⟩ := D.exists_good_le K
    exact ⟨L, D.isCompact L hL, hLK⟩
  have hdual := isAdmissible_smoothContragredient_of_compact_cofinal hcof ρ hρ
  exact D.admits_of_iwahoriContractions_of_splits ρ hUpper hLower hρ.1
    (fun K hK => powerKernelSup_isCompl_stableImage (smoothContragredient ρ)
      (isSmooth_smoothContragredient ρ) K (D.isCompact K hK) D.g (hdual.2 K))
    (fun K hK => powerKernelSup_isCompl_stableImage ρ hρ.1 K (D.isCompact K hK) D.g⁻¹
      (hρ.2 K))

/-- A chosen stable evaluation pairing, with its `Admits` input obtained from
admissibility and the two Iwahori contraction orientations. -/
def stablePairingOfIwahoriContractions :
    Coinvariants (smoothContragredient ρ) D.N →ₗ[ℂ]
      Coinvariants ρ D.Nbar →ₗ[ℂ] ℂ :=
  Classical.choose (D.exists_isStablePairing
    (D.admits_of_iwahoriContractions ρ hρ hUpper hLower))

/-- The chosen pairing satisfies the published stable evaluation law. -/
theorem stablePairingOfIwahoriContractions_isStablePairing :
    D.IsStablePairing ρ hρ.1
      (D.stablePairingOfIwahoriContractions ρ hρ hUpper hLower) :=
  Classical.choose_spec (D.exists_isStablePairing
    (D.admits_of_iwahoriContractions ρ hρ hUpper hLower))

/-- The chosen pairing is injective on the upper quotient of the smooth dual. -/
theorem stablePairingOfIwahoriContractions_injective :
    Function.Injective (D.stablePairingOfIwahoriContractions ρ hρ hUpper hLower) :=
  (D.stablePairingOfIwahoriContractions_isStablePairing ρ hρ hUpper hLower).injective
    (D.admits_of_iwahoriContractions ρ hρ hUpper hLower)

end Langlands.Jacquet.StablePairingData
