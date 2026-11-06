import Langlands.ClassFieldTheory.Local.ProfiniteReciprocityReconstruction
import Langlands.ClassFieldTheory.Local.FiniteArtinSystemStatement

/-! # Assembly of profinite reciprocity from a geometric finite Artin system -/

noncomputable section

namespace Langlands.LocalClassField

universe u

namespace ProfiniteReciprocityAssembly

open FiniteArtinReconstruction ProfiniteReciprocityReconstruction

/-- Restriction and reconstruction identify the two full geometric relations. -/
def geometricFamilyEquiv
    {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (T : F.TopologicalData) :
    letI := T.topology
    {r : F.Carrierˣ →ₜ* Field.absoluteGaloisGroupAbelianization F.Carrier //
      GeometricProfiniteReciprocityRelation F T r} ≃
    {a : FiniteArtinFamily F.Carrier // GeometricFiniteArtinSystemRelation F T a} := by
  letI := T.topology
  letI := Algebra.charZero_of_charZero (Padic p) F.Carrier
  exact
    { toFun r := ⟨finiteFamilyOfHom r.val, r.property.1.2, r.property.2⟩
      invFun a := ⟨reconstruct F.Carrier a.val a.property.1.2,
        reconstruct_geometric F T a.val a.property.1 a.property.2⟩
      left_inv r := Subtype.ext (finiteFamilyOfHom_injective F.Carrier
        (finiteFamilyOfHom_reconstruct F.Carrier (finiteFamilyOfHom r.val)
          r.property.1.2.2))
      right_inv a := Subtype.ext
        (finiteFamilyOfHom_reconstruct F.Carrier a.val a.property.1.2) }

/-- The unconditional finite-system theorem suffices for the unchanged profinite target. -/
theorem profiniteReciprocity_of_finiteArtin
    (h : GeometricFiniteArtinSystemExistenceUniqueness.{u}) :
    ProfiniteReciprocityExistenceUniqueness.{u} := by
  intro p hp F T
  let := T.topology
  let := Algebra.charZero_of_charZero (Padic p) F.Carrier
  obtain ⟨a, ha, huniq⟩ := h p F T
  refine ⟨reconstruct F.Carrier a ha.1.2,
    reconstruct_geometric F T a ha.1 ha.2, ?_⟩
  intro r hr
  apply finiteFamilyOfHom_injective F.Carrier
  exact (huniq (finiteFamilyOfHom r) ⟨hr.1.2, hr.2⟩).trans
    (finiteFamilyOfHom_reconstruct F.Carrier a ha.1.2).symm

end ProfiniteReciprocityAssembly

end Langlands.LocalClassField
