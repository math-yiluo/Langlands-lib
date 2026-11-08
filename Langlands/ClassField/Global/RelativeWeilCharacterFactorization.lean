import Langlands.ClassField.Global.RelativeWeilCharacterFactorizationStatement
import Langlands.ClassField.Global.RelativeWeilTransferReciprocityProof
import Langlands.Global.AdelicFunctoriality.IdeleNormOpen

/-!
# Continuous characters of relative Weil groups factor through the transfer

The transfer `W_{E/F} → C_F` agrees with the idele-class norm on the open subgroup `C_E`
(`transfer_inclusion`). The norm is continuous and open (`isOpenMap_ideleClassNorm`), so the
transfer is continuous and open. At an arithmetic class family it is surjective with kernel
the commutator subgroup (`relativeWeilTransferReciprocity`), hence a quotient map through
which every continuous character of `W_{E/F}` factors continuously. This proves
`TransferCharacterFactorizationStatement`.
-/

noncomputable section

set_option autoImplicit false

universe u

namespace Langlands.ClassField.Global.RelativeWeilGroup

open NumberField Topology Filter
open scoped NumberField
open Langlands.Global.AdelicFunctoriality

attribute [local instance] relativeGaloisTopology

variable (c : FundamentalClass.ClassFamily.{u}) (F E : Type u)
  [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E]

/-- The transfer composed with the inclusion of `C_E` is the idele-class norm. -/
theorem transfer_comp_inclusion :
    (transfer c F E) ∘ (inclusion c F E) = ideleClassNorm (K := F) (L := E) :=
  funext (transfer_inclusion c F E)

/-- The transfer `W_{E/F} → C_F` is continuous: near `1` it is the idele-class norm on the
open subgroup `C_E`. -/
theorem continuous_transfer' : Continuous (transfer c F E) := by
  refine continuous_of_continuousAt_one (transfer c F E) ?_
  have h := (isOpenEmbedding_inclusion c F E).continuousAt_iff (g := transfer c F E)
    (x := (1 : IdeleClassGroup (𝓞 E) E))
  rw [map_one] at h
  rw [← h, transfer_comp_inclusion]
  exact (ideleClassNorm (K := F) (L := E)).continuous.continuousAt

/-- The transfer `W_{E/F} → C_F` as a continuous homomorphism. -/
def continuousTransfer : RelativeWeilGroup c F E →ₜ* IdeleClassGroup (𝓞 F) F where
  toMonoidHom := transfer c F E
  continuous_toFun := continuous_transfer' c F E

@[simp]
theorem continuousTransfer_apply (t : RelativeWeilGroup c F E) :
    continuousTransfer c F E t = transfer c F E t :=
  rfl

/-- The transfer `W_{E/F} → C_F` is an open map, because the idele-class norm is. -/
theorem isOpenMap_transfer : IsOpenMap (transfer c F E) := by
  rw [IsTopologicalGroup.isOpenMap_iff_nhds_one]
  have hN := (IsTopologicalGroup.isOpenMap_iff_nhds_one
    (f := ideleClassNorm (K := F) (L := E))).mp isOpenMap_ideleClassNorm
  have hI := (isOpenEmbedding_inclusion c F E).map_nhds_eq 1
  rw [map_one] at hI
  calc 𝓝 (1 : IdeleClassGroup (𝓞 F) F)
      ≤ map (ideleClassNorm (K := F) (L := E)) (𝓝 1) := hN
    _ = map (transfer c F E) (map (inclusion c F E) (𝓝 1)) := by
      rw [map_map, transfer_comp_inclusion]
    _ = map (transfer c F E) (𝓝 1) := by rw [hI]

/-- A surjective transfer is a quotient map. -/
theorem isQuotientMap_transfer (hsurj : Function.Surjective (transfer c F E)) :
    IsQuotientMap (transfer c F E) :=
  (isOpenMap_transfer c F E).isQuotientMap (continuous_transfer' c F E) hsurj

/-- When the transfer is surjective with kernel in the commutator subgroup, every continuous
character of `W_{E/F}` is a continuous character of `C_F` composed with the transfer. -/
theorem transferCharacterFactorization_of_surjective
    (hsurj : Function.Surjective (transfer c F E))
    (hker : (transfer c F E).ker ≤ commutator (RelativeWeilGroup c F E)) :
    TransferCharacterFactorization c F E := by
  intro ξ
  have hξ : (transfer c F E).ker ≤ (ξ : RelativeWeilGroup c F E →* ℂˣ).ker :=
    hker.trans (Abelianization.commutator_subset_ker _)
  let χ₀ : IdeleClassGroup (𝓞 F) F →* ℂˣ :=
    (transfer c F E).liftOfSurjective hsurj ⟨ξ, hξ⟩
  have hχ₀ : ∀ t, χ₀ (transfer c F E t) = ξ t := fun t =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ t
  have hcont : Continuous χ₀ := by
    rw [(isQuotientMap_transfer c F E hsurj).continuous_iff]
    have h : (χ₀ : IdeleClassGroup (𝓞 F) F → ℂˣ) ∘ (transfer c F E) = ξ := funext hχ₀
    rw [h]
    exact ξ.continuous
  exact ⟨⟨χ₀, hcont⟩, fun t => (hχ₀ t).symm⟩

/-- Tate (1979), (1.1), for relative Weil groups at an arithmetic class family: every
continuous character of `W_{E/F}` factors through the transfer as a continuous character of
`C_F`. -/
theorem transferCharacterFactorization : TransferCharacterFactorizationStatement.{u} := by
  intro c hc F E _ _ _ _ _ _
  obtain ⟨I, hI, hgen, hres, hinf, hloc⟩ := hc
  have h := relativeWeilTransferReciprocity I hI c ⟨hgen, hres, hinf, hloc⟩ F E
  exact transferCharacterFactorization_of_surjective c F E h.1 h.2.le

end Langlands.ClassField.Global.RelativeWeilGroup
