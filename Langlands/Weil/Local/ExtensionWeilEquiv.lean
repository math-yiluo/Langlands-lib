import Langlands.Weil.Local.ExtensionWeilRange

/-!
# The local Weil map of an isomorphism of p-adic fields

For a `ℚ_p`-algebra isomorphism `f : F ≅ E` the local Weil map
`extensionWeilMap F E f : W_E → W_F` is an isomorphism of topological groups.
-/

noncomputable section

namespace Langlands.Weil.Local

universe u v

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
variable (f : F.Carrier ≃ₐ[Padic p] E.Carrier)

/-- A p-adic algebra isomorphism has extension degree one. -/
@[simp] theorem extensionDegree_algEquiv :
    extensionDegree F E f.toAlgHom = 1 := by
  have h := finrank_mul_extensionDegree F E f.toAlgHom
  rw [← f.toLinearEquiv.finrank_eq] at h
  exact Nat.eq_of_mul_eq_mul_left (Module.finrank_pos (R := Padic p) (M := F.Carrier))
    (h.trans (mul_one _).symm)

/-- The image of `W_E` is all of `W_F` when `f` is an isomorphism. -/
theorem extensionWeilRange_algEquiv : extensionWeilRange F E f.toAlgHom = ⊤ := by
  apply Subgroup.index_eq_one.mp
  rw [extensionWeilRange_index, extensionDegree_algEquiv]

theorem extensionWeilMap_surjective_algEquiv :
    Function.Surjective (extensionWeilMap F E f.toAlgHom) := by
  intro x
  have hx : x ∈ extensionWeilRange F E f.toAlgHom := by
    rw [extensionWeilRange_algEquiv]
    exact Subgroup.mem_top x
  obtain ⟨w, hw⟩ := hx
  exact ⟨w, hw⟩

/-- The local Weil map `W_E → W_F` of a `ℚ_p`-algebra isomorphism `F ≅ E`,
as an isomorphism of topological groups. -/
def extensionWeilEquiv : localWeilGroup E ≃ₜ* localWeilGroup F :=
  (extensionWeilRangeEquiv F E f.toAlgHom).trans
    { toMulEquiv :=
        (MulEquiv.subgroupCongr (extensionWeilRange_algEquiv F E f)).trans Subgroup.topEquiv
      continuous_toFun := continuous_subtype_val
      continuous_invFun := continuous_id.subtype_mk _ }

@[simp] theorem extensionWeilEquiv_apply (w : localWeilGroup E) :
    extensionWeilEquiv F E f w = extensionWeilMap F E f.toAlgHom w := rfl

theorem coe_extensionWeilEquiv :
    ((extensionWeilEquiv F E f : localWeilGroup E →ₜ* localWeilGroup F)) =
      extensionWeilMap F E f.toAlgHom := rfl

end Langlands.Weil.Local
