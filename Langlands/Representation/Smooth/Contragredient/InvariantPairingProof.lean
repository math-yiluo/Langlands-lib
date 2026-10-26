import Langlands.Representation.Smooth.Contragredient.InvariantPairingStatement
import Langlands.Representation.Smooth.Contragredient.LawsProof
import Langlands.Representation.Smooth.Contragredient.AdmissibleDualityProof
import Langlands.Representation.Smooth.Contragredient.ExactProof
import Langlands.Representation.Smooth.Admissibility.EmbeddingProof

/-! # Perfectness of an invariant pairing with one admissible side -/

noncomputable section

namespace Langlands

universe uG uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- Two-sided nondegeneracy and one-sided admissibility make the supplied
invariant pairing an equivalence with the actual smooth dual. -/
theorem smoothInvariantPairingDuality :
    SmoothInvariantPairingDualityStatement (G := G) (V := V) (W := W) := by
  intro _ hcofinal ρ σ hρ hσ b hinv hleft hright
  let F₀ : σ.IntertwiningMap ρ.dual :=
    { toLinearMap := b
      isIntertwining' := by
        intro g
        ext w v
        change b (σ g w) v = b w (ρ g⁻¹ v)
        simpa only [ρ.self_inv_apply] using hinv g w (ρ g⁻¹ v) }
  let F : σ.IntertwiningMap (smoothContragredient ρ) := smoothLift hσ F₀
  let C₀ : ρ.IntertwiningMap σ.dual :=
    { toLinearMap := b.flip
      isIntertwining' := by
        intro g
        ext v w
        change b w (ρ g v) = b (σ g⁻¹ w) v
        simpa only [σ.self_inv_apply] using hinv g (σ g⁻¹ w) v }
  let C : ρ.IntertwiningMap (smoothContragredient σ) := smoothLift hρ.1 C₀
  have hFzero (w : W) (hw : F w = 0) : w = 0 := by
    apply hleft w
    intro v
    exact congrArg (fun ℓ : SmoothDual ρ => ℓ.val v) hw
  have hF : Function.Injective F := by
    intro w w' h
    apply sub_eq_zero.mp
    apply hFzero
    rw [map_sub, h, sub_self]
  have hCzero (v : V) (hv : C v = 0) : v = 0 := by
    apply hright v
    intro w
    exact congrArg (fun ℓ : SmoothDual σ => ℓ.val w) hv
  have hC : Function.Injective C := by
    intro v v' h
    apply sub_eq_zero.mp
    apply hCzero
    rw [map_sub, h, sub_self]
  have hσadmissible : IsAdmissible σ :=
    isAdmissible_of_injective F hF
      (isAdmissible_smoothContragredient_of_compact_cofinal hcofinal ρ hρ)
  have hDC : Function.Surjective (contragredientMap C) :=
    contragredientMap_surjective_of_injective_of_compact_cofinal hcofinal
      hρ.1 (isSmooth_smoothContragredient σ) C hC
  have hbidual : Function.Surjective (smoothBidual hσ) :=
    smoothBidual_surjective_of_compact_cofinal hcofinal σ hσadmissible
  have hFsurjective : Function.Surjective F := by
    intro ℓ
    obtain ⟨ψ, hψ⟩ := hDC ℓ
    obtain ⟨w, hw⟩ := hbidual ψ
    refine ⟨w, ?_⟩
    calc
      F w = contragredientMap C (smoothBidual hσ w) := by
        apply Subtype.ext
        apply LinearMap.ext
        intro v
        rfl
      _ = contragredientMap C ψ := congrArg (contragredientMap C) hw
      _ = ℓ := hψ
  refine ⟨F.ofBijective ⟨hF, hFsurjective⟩, ?_⟩
  intro w v
  rfl

end Langlands
