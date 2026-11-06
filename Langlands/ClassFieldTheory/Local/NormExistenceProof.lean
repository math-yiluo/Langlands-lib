import Langlands.ClassFieldTheory.Local.NormExistenceOrder
import Langlands.ClassFieldTheory.Local.NormExistenceCompactSupport
import Langlands.ClassFieldTheory.Local.NormExistenceUnramifiedSupport
import Langlands.ClassFieldTheory.Local.UniversalNormFiniteIndex

/-! # The local norm-subgroup existence theorem -/

noncomputable section

namespace Langlands.ClassFieldTheory.Local

universe u

open Langlands.LocalClassField

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048

variable {p : ℕ} [Fact p.Prime]

/-- Every open finite-index subgroup contains a finite abelian norm group. -/
theorem exists_finiteAbelian_normSubgroup_le (F : PadicField.{u} p)
    (H : Subgroup F.Carrierˣ)
    (hH : let := F.canonicalTopologicalData.topology
      IsOpen (H : Set F.Carrierˣ)) [H.FiniteIndex] :
    ∃ E : FiniteIntermediateExtension F.Carrier,
      IsAbelianGalois F.Carrier E.field ∧ normSubgroup F.Carrier E.field ≤ H := by
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let 𝒩 := finiteAbelianNormFamily F.Carrier
  let U := T.unitSubgroup
  have hU : IsCompact (U : Set F.Carrierˣ) := by
    rw [show U = T.unitFiltration 0 from T.unitFiltration_zero.symm]
    exact T.isCompact_unitFiltration 0
  have hinter : ∀ x : F.Carrierˣ, (∀ N ∈ 𝒩, x ∈ N) → x ∈ H := by
    intro x hx
    exact universalNorm_le_finiteIndex F H
      ((mem_universalNormSubgroup_iff F.Carrier x).mpr hx)
  obtain ⟨N, hN, hNU⟩ := exists_subgroup_inf_le_of_compact
    𝒩 (finiteAbelianNormFamily_nonempty F.Carrier)
    (finiteAbelianNormFamily_directed F.Carrier)
    (isClosed_finiteAbelianNormFamily F T) U H hU hH hinter
  have hNindex : N.FiniteIndex := by
    obtain ⟨E, hE, rfl⟩ := hN
    let := hE
    exact finiteIndex_normSubgroup F E.field
  let : N.FiniteIndex := hNindex
  let V := U ⊔ (N ⊓ H)
  let : V.FiniteIndex := Subgroup.finiteIndex_of_le (H := N ⊓ H) le_sup_right
  obtain ⟨L, hL, _, _, hLV⟩ := exists_unramified_normSubgroup_le F V le_sup_left
  have hLmem : normSubgroup F.Carrier L.field ∈ 𝒩 := ⟨L, hL, rfl⟩
  obtain ⟨D, hD, hDN, hDL⟩ := finiteAbelianNormFamily_directed F.Carrier N hN
    (normSubgroup F.Carrier L.field) hLmem
  obtain ⟨E, hE, rfl⟩ := hD
  refine ⟨E, hE, ?_⟩
  intro x hx
  exact inf_sup_inf_le_of_inf_le N U H hNU ⟨hDN hx, hLV (hDL hx)⟩

/-- Every open finite-index subgroup is the norm group of a unique finite
abelian intermediate extension in the actual algebraic closure. -/
theorem normSubgroupExistence : NormSubgroupExistence.{u} := by
  intro p hp F H hH hHindex
  let : H.FiniteIndex := hHindex
  obtain ⟨M, hMab, hMH⟩ := exists_finiteAbelian_normSubgroup_le F H hH
  let := hMab
  obtain ⟨E, hEfd, hEab, hEN⟩ :=
    exists_normSubgroup_eq_of_le_finite_abelian F M.field H hMH
  let := hEfd
  let := hEab
  let E' := IntermediateField.lift E
  let e : E ≃ₐ[F.Carrier] E' := IntermediateField.liftAlgEquiv E
  let : FiniteDimensional F.Carrier E' := LinearEquiv.finiteDimensional e.toLinearEquiv
  let : IsAbelianGalois F.Carrier E' := IsAbelianGalois.of_algHom e.symm.toAlgHom
  have hn : normSubgroup F.Carrier E' = H := by
    rw [← normSubgroup_eq_of_baseAlgEquiv F.Carrier E E' e]
    exact hEN
  refine ⟨E', ⟨inferInstance, inferInstance, hn⟩, ?_⟩
  rintro D ⟨hDfd, hDab, hDN⟩
  let := hDfd
  let := hDab
  exact finiteAbelian_eq_of_normSubgroup_eq F (AlgebraicClosure F.Carrier) D E'
    (hDN.trans hn.symm)

end Langlands.ClassFieldTheory.Local
