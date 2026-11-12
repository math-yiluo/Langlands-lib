import Langlands.ClassFieldTheory.Local.Transfer
import Langlands.LocalClassField.AbelianizationTransport
import Langlands.GroupTheory.TransferDoubleCoset

/-! # Naturality of actual transfer through a continuous map with dense range -/

noncomputable section

namespace Langlands.LocalClassField.TransferNaturality

universe u v w

variable {G : Type u} {L : Type v} [Group G] [Group L]
  [TopologicalSpace G] [TopologicalSpace L] [IsTopologicalGroup G] [IsTopologicalGroup L]
  (f : L →ₜ* G) (H : Subgroup G)

/-- The restriction of a continuous homomorphism from a subgroup preimage to that subgroup. -/
def subgroupPreimageMap : H.comap f.toMonoidHom →ₜ* H where
  toMonoidHom := f.toMonoidHom.subgroupComap H
  continuous_toFun := (f.continuous.comp continuous_subtype_val).subtype_mk _

omit [IsTopologicalGroup L] in
/-- A dense group image meets every coset of an open subgroup. -/
theorem exists_mul_of_denseRange (hf : DenseRange f) (hH : IsOpen (H : Set G)) (g : G) :
    ∃ l : L, ∃ h ∈ H, g = f l * h := by
  let V : Set G := {x | x⁻¹ * g ∈ H}
  have hVo : IsOpen V := hH.preimage (continuous_inv.mul continuous_const)
  have hV : V.Nonempty := ⟨g, by simp [V]⟩
  obtain ⟨l, hl⟩ := hf.exists_mem_open hVo hV
  refine ⟨l, (f l)⁻¹ * g, hl, ?_⟩
  simp

omit [IsTopologicalGroup L] in
/-- Actual coset-product transfer commutes with a dense continuous group map
when the target subgroup is open. -/
theorem transfer_comp_denseRange {A : Type w} [CommGroup A]
    [H.FiniteIndex] (hf : DenseRange f) (hH : IsOpen (H : Set G))
    (ϕ : H →* A) (y : L) :
    MonoidHom.transfer ϕ (f y) =
      MonoidHom.transfer (ϕ.comp (subgroupPreimageMap f H).toMonoidHom) y := by
  have hK : ∀ (_ : Unit) (l : L), l ∈ H.comap f.toMonoidHom ↔
      (1 : G)⁻¹ * f l * 1 ∈ H := by
    intro _ l
    simp
  change MonoidHom.transfer ϕ (f.toMonoidHom y) = _
  rw [GroupTheory.Transfer.transfer_comp_eq_prod_of_conj
    (ψ := f.toMonoidHom) (t := fun _ : Unit => (1 : G))
    (K := fun _ : Unit => H.comap f.toMonoidHom) (hK := hK) ϕ
    (fun _ => ϕ.comp (subgroupPreimageMap f H).toMonoidHom) ?_ ?_ ?_ y,
    Fintype.prod_unique]
  · intro _ k
    change ϕ (subgroupPreimageMap f H k) = _
    apply congrArg ϕ
    apply Subtype.ext
    change f k = (1 : G)⁻¹ * f k * 1
    simp
  · intro g
    obtain ⟨l, h, hh, hg⟩ := exists_mul_of_denseRange f H hf hH g
    exact ⟨(), l, h, hh, by simpa using hg⟩
  · intro _ _ _ _ _ _
    rfl

/-- The continuous transfer square descends to the actual closed-commutator quotients. -/
theorem abelianizedTransfer_naturality [H.FiniteIndex]
    (hf : DenseRange f) (hH : IsOpen (H : Set G)) :
    (abelianizedTransfer H hH).comp (abelianizationMap f) =
      (abelianizationMap (subgroupPreimageMap f H)).comp
        (abelianizedTransfer (H.comap f.toMonoidHom) (hH.preimage f.continuous)) := by
  apply abelianization_hom_ext
  intro y
  change MonoidHom.transfer (abelianizationProjection H).toMonoidHom (f y) =
    abelianizationMap (subgroupPreimageMap f H)
      (MonoidHom.transfer (abelianizationProjection (H.comap f.toMonoidHom)).toMonoidHom y)
  rw [transfer_comp_denseRange f H hf hH]
  exact GroupTheory.Transfer.transfer_comp
    (abelianizationProjection (H.comap f.toMonoidHom)).toMonoidHom
    (abelianizationMap (subgroupPreimageMap f H)).toMonoidHom y

end Langlands.LocalClassField.TransferNaturality
