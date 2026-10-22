import Langlands.Weil.Local.ExtensionWeil

/-!
# The local Weil group of an extension as an open subgroup
-/

noncomputable section

namespace Langlands.Weil.Local

universe u v

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
variable (f : F.Carrier →ₐ[Padic p] E.Carrier)

/-- The image of `W_E` in `W_F` under the local Weil map. -/
abbrev extensionWeilRange : Subgroup (localWeilGroup F) :=
  (extensionWeilMap F E f).toMonoidHom.range

/-- `W_E` is isomorphic, as a topological group, to its image in `W_F`. -/
def extensionWeilRangeEquiv : localWeilGroup E ≃ₜ* extensionWeilRange F E f where
  toMulEquiv := MonoidHom.ofInjective (f := (extensionWeilMap F E f).toMonoidHom)
    (extensionWeilMap_injective F E f)
  continuous_toFun := (extensionWeilMap F E f).continuous.subtype_mk _
  continuous_invFun := by
    rw [(extensionWeilMap_isEmbedding F E f).isInducing.continuous_iff]
    convert continuous_subtype_val using 1
    funext x
    exact MonoidHom.apply_ofInjective_symm (extensionWeilMap_injective F E f) x

@[simp] theorem extensionWeilRangeEquiv_apply (w : localWeilGroup E) :
    (extensionWeilRangeEquiv F E f w : localWeilGroup F) = extensionWeilMap F E f w := rfl

@[simp] theorem extensionWeilMap_extensionWeilRangeEquiv_symm (x : extensionWeilRange F E f) :
    extensionWeilMap F E f ((extensionWeilRangeEquiv F E f).symm x) = x :=
  MonoidHom.apply_ofInjective_symm (extensionWeilMap_injective F E f) x

/-- On the image of `W_E`, the projection of `F` is the Galois map applied to that of `E`. -/
theorem localProjection_extensionWeilRange (x : extensionWeilRange F E f) :
    localProjection F x =
      extensionGaloisMap F E f (localProjection E ((extensionWeilRangeEquiv F E f).symm x)) := by
  rw [← localProjection_extensionWeilMap, extensionWeilMap_extensionWeilRangeEquiv_symm]

/-- On the image of `W_E`, the norm character of `F` is that of `E`. -/
theorem localNormCharacter_extensionWeilRange (x : extensionWeilRange F E f) :
    localNormCharacter F x = localNormCharacter E ((extensionWeilRangeEquiv F E f).symm x) := by
  rw [← localNormCharacter_extensionWeilMap F E f,
    extensionWeilMap_extensionWeilRangeEquiv_symm]

/-- The image of `W_E` is an open subgroup of `W_F`. -/
def extensionWeilOpenSubgroup : OpenSubgroup (localWeilGroup F) where
  toSubgroup := extensionWeilRange F E f
  isOpen' := extensionWeilMap_range_isOpen F E f

/-- The open image of `W_E` has index `[E : F]`. -/
theorem extensionWeilRange_index :
    (extensionWeilRange F E f).index = extensionDegree F E f :=
  extensionWeilMap_range_index F E f

instance extensionWeilRange_finiteIndex : (extensionWeilRange F E f).FiniteIndex :=
  extensionWeilMap_range_finiteIndex F E f

/-- Inertia of `F` meets the image of `W_E` exactly in the image of the inertia of `E`. -/
theorem localInertia_inf_extensionWeilRange :
    localInertia F ⊓ extensionWeilRange F E f =
      (localInertia E).map (extensionWeilMap F E f).toMonoidHom := by
  ext x
  constructor
  · rintro ⟨hI, w, rfl⟩
    exact ⟨w, (extensionWeilMap_mem_localInertia F E f w).mp hI, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨(extensionWeilMap_mem_localInertia F E f w).mpr hw, w, rfl⟩

end Langlands.Weil.Local
