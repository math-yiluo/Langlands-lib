import Langlands.Representation.Smooth.Contragredient.AdmissibleDualityProof
import Langlands.Representation.Smooth.Contragredient.LawsProof

/-!
# Intertwiners represented by weak forms

When compact open subgroups are cofinal, a bilinear pairing between a smooth
representation and the smooth dual of an admissible representation that obeys
the contragredient translation law is the pairing of an actual intertwiner.
The proof inverts the evaluation map into the double smooth contragredient.
-/

noncomputable section

namespace Langlands

universe uG uX uY

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {X : Type uX} [AddCommGroup X] [Module ℂ X]
variable {Y : Type uY} [AddCommGroup Y] [Module ℂ Y]

/-- A bilinear form `Λ(y, ℓ)` on a smooth representation `π` and the smooth dual
of an admissible representation `τ` with `Λ(π(h)y, ℓ) = Λ(y, τ̃(h⁻¹)ℓ)` is
`ℓ(f(y))` for an intertwiner `f : π → τ`. -/
theorem exists_intertwiningMap_of_weakForm_of_compact_cofinal
    (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)
    {π : Representation ℂ G Y} (hπ : IsSmooth π)
    {τ : Representation ℂ G X} (hτ : IsAdmissible τ)
    (Λ : Y →ₗ[ℂ] SmoothDual τ →ₗ[ℂ] ℂ)
    (hΛ : ∀ (h : G) (y : Y) (ℓ : SmoothDual τ),
      Λ (π h y) ℓ = Λ y (smoothContragredient τ h⁻¹ ℓ)) :
    ∃ f : π.IntertwiningMap τ, ∀ (y : Y) (ℓ : SmoothDual τ),
      smoothDualPairing τ ℓ (f y) = Λ y ℓ := by
  have hsm : ∀ y : Y, Λ y ∈ smoothVectors (smoothContragredient τ).dual := by
    intro y
    obtain ⟨K, hK⟩ := hπ y
    refine ⟨K, fun k => ?_⟩
    have hk : π (k : G) y = y := hK k
    apply LinearMap.ext
    intro ℓ
    change Λ y (smoothContragredient τ (k : G)⁻¹ ℓ) = Λ y ℓ
    rw [← hΛ, hk]
  let Φ : π.IntertwiningMap
      (smoothContragredient (V := SmoothDual τ) (smoothContragredient τ)) :=
    { toLinearMap := Λ.codRestrict _ hsm
      isIntertwining' := by
        intro h
        apply LinearMap.ext
        intro y
        apply Subtype.ext
        apply LinearMap.ext
        intro ℓ
        exact hΛ h y ℓ }
  let e := (smoothBidual hτ.1).ofBijective
    ⟨smoothBidual_injective_of_compact_cofinal hcof τ hτ.1,
      smoothBidual_surjective_of_compact_cofinal hcof τ hτ⟩
  refine ⟨e.symm.toIntertwiningMap.comp Φ, fun y ℓ => ?_⟩
  rw [← smoothBidual_apply hτ.1]
  have he : smoothBidual hτ.1 (e.symm (Φ y)) = Φ y := e.apply_symm_apply (Φ y)
  change smoothDualPairing (smoothContragredient τ)
    (smoothBidual hτ.1 (e.symm (Φ y))) ℓ = Λ y ℓ
  rw [he]
  rfl

end Langlands
