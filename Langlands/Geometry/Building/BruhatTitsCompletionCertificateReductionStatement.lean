import Langlands.Geometry.Building.BruhatTitsAvailabilityStatement
import Langlands.Geometry.Building.BruhatTitsCompletionCertificateStatement
import Langlands.Geometry.Building.UnramifiedDescentOfGroupAxiomsStatement

/-! # The full certificate from availability and unramified descent -/

universe u

open AlgebraicGeometry

namespace Langlands.Geometry.Building

/-- Availability and the existence of equivalent group-valid descended data
together imply the completion certificate of KP Theorem 9.2.7. -/
def BruhatTitsCompletionCertificateReductionStatement : Prop :=
  BruhatTitsAvailabilityStatement.{u} →
    UnramifiedDescentOfGroupAxiomsStatement.{u} →
      BruhatTitsCompletionCertificateStatement.{u}

/-- Choose the descended data and transfer the comparisons from the valid assignment. -/
theorem bruhatTitsCompletionCertificateReduction :
    BruhatTitsCompletionCertificateReductionStatement.{u} := by
  classical
  intro hAvailability hDescent
  obtain ⟨𝔅, hValid⟩ := hAvailability
  have hDatum (p : KPBuildingAssignment.DatumIndex.{u}) :=
    hDescent p (𝔅.datumAt p) (hValid p.F p.G p.reductive).groupAxioms
  choose D hGroup hUnramified hEquiv using hDatum
  refine ⟨KPBuildingAssignment.ofData D, KPBuildingAssignment.ofData_isValid
    𝔅 hValid D hGroup (fun p => Classical.choice (hEquiv p)), ?_⟩
  intro F _ _ _ _ G _ hG
  exact hUnramified ⟨F, ‹Field F›, ‹ValuativeRel F›, ‹TopologicalSpace F›,
    ‹IsNonarchimedeanLocalField F›, G, ‹IsAffineHom G.X.hom›, hG⟩

end Langlands.Geometry.Building
