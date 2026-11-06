import Langlands.ClassFieldTheory.Local.NormExistenceFiniteLattice

/-! # Order reflection and uniqueness for finite abelian norm groups -/

noncomputable section

namespace Langlands.ClassFieldTheory.Local

universe u v w

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048

/-- An algebra equivalence preserves the actual determinant-norm subgroup. -/
theorem normSubgroup_eq_of_baseAlgEquiv (K : Type u) (L : Type v) (M : Type w)
    [Field K] [Field L] [Field M] [Algebra K L] [Algebra K M]
    [FiniteDimensional K L] [FiniteDimensional K M] (e : L ≃ₐ[K] M) :
    Langlands.LocalClassField.normSubgroup K L =
      Langlands.LocalClassField.normSubgroup K M := by
  apply le_antisymm
  · rintro _ ⟨a, rfl⟩
    refine ⟨Units.map e.toMonoidHom a, ?_⟩
    apply Units.ext
    exact Algebra.norm_eq_of_algEquiv e (a : L)
  · rintro _ ⟨a, rfl⟩
    refine ⟨Units.map e.symm.toMonoidHom a, ?_⟩
    apply Units.ext
    exact Algebra.norm_eq_of_algEquiv e.symm (a : M)

variable {p : ℕ} [Fact p.Prime]

/-- Inside a finite abelian extension, norm subgroups reflect the reversed field order. -/
theorem intermediateField_le_iff_normSubgroup_le
    (F : PadicField.{u} p) (M : Type u) [Field M]
    [Algebra F.Carrier M] [FiniteDimensional F.Carrier M]
    [IsAbelianGalois F.Carrier M] (E₁ E₂ : IntermediateField F.Carrier M) :
    E₁ ≤ E₂ ↔ Langlands.LocalClassField.normSubgroup F.Carrier E₂ ≤
      Langlands.LocalClassField.normSubgroup F.Carrier E₁ := by
  obtain ⟨I, _, _, _, _, _, hFund, _, _, _, _, hTate, _, hTransfers, _, _⟩ :=
    localAbsoluteCorestrictionCompatibleClassFormation p
  let q := Langlands.LocalClassField.normQuotientProjection F.Carrier M
  let e := abelianNormCorrespondenceEquiv I hFund hTate F M
  have hk : q.ker ≤ Langlands.LocalClassField.normSubgroup F.Carrier E₁ := by
    change (QuotientGroup.mk' (Langlands.LocalClassField.normSubgroup F.Carrier M)).ker ≤ _
    rw [QuotientGroup.ker_mk']
    exact normSubgroup_le_of_tower F.Carrier M E₁
  have himage :
      (Langlands.LocalClassField.normSubgroup F.Carrier E₂).map q ≤
          (Langlands.LocalClassField.normSubgroup F.Carrier E₁).map q ↔
        E₂.fixingSubgroup ≤ E₁.fixingSubgroup := by
    rw [normSubgroup_map_eq_fixingSubgroup_map I hFund hTate hTransfers F M E₂,
      normSubgroup_map_eq_fixingSubgroup_map I hFund hTate hTransfers F M E₁]
    exact Subgroup.map_le_map_iff_of_injective e.injective
  rw [Subgroup.map_le_map_iff (f := q), sup_eq_left.mpr hk] at himage
  exact (IsGalois.intermediateFieldEquivSubgroup (F := F.Carrier) (E := M)).map_rel_iff'.symm.trans
    himage.symm

/-- The norm subgroup map on the subfields of a finite abelian extension is an order embedding. -/
def finiteAbelianNormOrderEmbedding (F : PadicField.{u} p) (M : Type u) [Field M]
    [Algebra F.Carrier M] [FiniteDimensional F.Carrier M]
    [IsAbelianGalois F.Carrier M] :
    IntermediateField F.Carrier M ↪o (Subgroup F.Carrierˣ)ᵒᵈ where
  toFun E := OrderDual.toDual (Langlands.LocalClassField.normSubgroup F.Carrier E)
  inj' E₁ E₂ h := le_antisymm
    ((intermediateField_le_iff_normSubgroup_le F M E₁ E₂).mpr (le_of_eq h.symm))
    ((intermediateField_le_iff_normSubgroup_le F M E₂ E₁).mpr (le_of_eq h))
  map_rel_iff' := (intermediateField_le_iff_normSubgroup_le F M _ _).symm

/-- Finite abelian subfields of any common ambient field have the reversed norm order. -/
theorem finiteAbelian_le_iff_normSubgroup_le (F : PadicField.{u} p)
    (L : Type u) [Field L] [Algebra F.Carrier L]
    (E₁ E₂ : IntermediateField F.Carrier L)
    [FiniteDimensional F.Carrier E₁] [FiniteDimensional F.Carrier E₂]
    [IsAbelianGalois F.Carrier E₁] [IsAbelianGalois F.Carrier E₂] :
    E₁ ≤ E₂ ↔ Langlands.LocalClassField.normSubgroup F.Carrier E₂ ≤
      Langlands.LocalClassField.normSubgroup F.Carrier E₁ := by
  let M := E₁ ⊔ E₂
  let D₁ : IntermediateField F.Carrier M := IntermediateField.restrict le_sup_left
  let D₂ : IntermediateField F.Carrier M := IntermediateField.restrict le_sup_right
  have hn₁ := normSubgroup_eq_of_baseAlgEquiv F.Carrier E₁ D₁
    (IntermediateField.restrictAlgEquiv le_sup_left)
  have hn₂ := normSubgroup_eq_of_baseAlgEquiv F.Carrier E₂ D₂
    (IntermediateField.restrictAlgEquiv le_sup_right)
  rw [hn₁, hn₂, ← intermediateField_le_iff_normSubgroup_le F M D₁ D₂]
  constructor
  · intro h x hx
    exact (IntermediateField.mem_restrict le_sup_right x).mpr
      (h ((IntermediateField.mem_restrict le_sup_left x).mp hx))
  · intro h x hx
    let y : M := ⟨x, (show E₁ ≤ M from le_sup_left) hx⟩
    exact (IntermediateField.mem_restrict le_sup_right y).mp
      (h ((IntermediateField.mem_restrict le_sup_left y).mpr hx))

/-- Equality of norm groups determines a finite abelian intermediate field uniquely. -/
theorem finiteAbelian_eq_of_normSubgroup_eq (F : PadicField.{u} p)
    (L : Type u) [Field L] [Algebra F.Carrier L]
    (E₁ E₂ : IntermediateField F.Carrier L)
    [FiniteDimensional F.Carrier E₁] [FiniteDimensional F.Carrier E₂]
    [IsAbelianGalois F.Carrier E₁] [IsAbelianGalois F.Carrier E₂]
    (h : Langlands.LocalClassField.normSubgroup F.Carrier E₁ =
      Langlands.LocalClassField.normSubgroup F.Carrier E₂) : E₁ = E₂ := by
  exact le_antisymm
    ((finiteAbelian_le_iff_normSubgroup_le F L E₁ E₂).mpr h.ge)
    ((finiteAbelian_le_iff_normSubgroup_le F L E₂ E₁).mpr h.le)

end Langlands.ClassFieldTheory.Local
