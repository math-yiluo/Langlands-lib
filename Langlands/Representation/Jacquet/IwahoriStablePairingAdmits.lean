import Langlands.Representation.Jacquet.StablePairingProof
import Langlands.Representation.Jacquet.IwahoriContractionAdmissibility
import Langlands.Representation.Smooth.Contragredient.AdmissibleDualityProof

/-! Admissibility supplies the stable-pairing hypotheses under both Iwahori
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
for an admissible representation. No representation-theoretic lift hypothesis
is required as an additional input. -/
theorem admits_of_iwahoriContractions : D.Admits ρ hρ.1 := by
  have hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L ≤ K := by
    intro K
    obtain ⟨L, hL, hLK⟩ := D.exists_good_le K
    exact ⟨L, D.isCompact L hL, hLK⟩
  have hdual := isAdmissible_smoothContragredient_of_compact_cofinal hcof ρ hρ
  exact
    { finite := fun K _ => hρ.2 K
      upper_surjective := fun K hK =>
        (stableImageJacquetMap_bijective_of_iwahoriContraction
          (smoothContragredient ρ) (isSmooth_smoothContragredient ρ)
          (D.isCompact K hK) (hUpper K hK) D.hMN (hdual.2 K)).2
      upper_kernel := fun K hK =>
        (powerKernelSup_eq_ker_of_iwahoriContraction
          (smoothContragredient ρ) (isSmooth_smoothContragredient ρ)
          (D.isCompact K hK) (hUpper K hK) D.hMN).ge
      lower_surjective := fun K hK =>
        (stableImageJacquetMap_bijective_of_iwahoriContraction ρ hρ.1
          (D.isCompact K hK) (hLower K hK) D.hMNbar (hρ.2 K)).2
      lower_kernel := fun K hK =>
        (powerKernelSup_eq_ker_of_iwahoriContraction ρ hρ.1
          (D.isCompact K hK) (hLower K hK) D.hMNbar).ge }

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
