import Langlands.AlgebraicGeometry.Modules.SerreVanishing.Devissage
import Langlands.AlgebraicGeometry.Modules.SerreVanishing.Dimension

/-! # Assembly of two-bundle Serre vanishing from section killing -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.Picard

namespace Langlands.AlgebraicGeometry.Modules

/-- The section-killing theorem is the remaining premise for the exact published target. -/
theorem properAmplePairSerreVanishing_of_sectionKilling
    (hkill : SerreVanishing.SectionKillingStatement.{u}) :
    ProperAmplePairSerreVanishingStatement.{u} := by
  intro K _ X f hf M hM hMf L₁ L₂ h₁ h₂
  let : IsProper f := hf
  let : M.IsQuasicoherent := hM
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : IsNoetherian X := ⟨⟩
  let : X.IsSeparated := ⟨by
    rw [← terminal.comp_from f]
    infer_instance⟩
  obtain ⟨d, hd⟩ := SerreVanishing.finiteTopologicalDimension f
  exact SerreVanishing.goodInSupportDimension hkill f L₁ L₂ h₁ h₂ (d + 1)
    M hM hMf (HasSupportDimensionLT.of_topologicalKrullDim_le hd M)

end Langlands.AlgebraicGeometry.Modules
