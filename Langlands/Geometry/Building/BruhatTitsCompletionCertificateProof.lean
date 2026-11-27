import Langlands.Geometry.Building.BruhatTitsAvailabilityProof
import Langlands.Geometry.Building.BruhatTitsCompletionCertificateReductionStatement
import Langlands.Geometry.Building.UnramifiedDescentOfGroupAxiomsProof

/-! # The Bruhat–Tits completion certificate over nonarchimedean local fields -/

universe u

namespace Langlands.Geometry.Building

/-- A single valid assignment of Bruhat–Tits data satisfies unramified descent
for every connected reductive group over a nonarchimedean local field. -/
theorem bruhatTitsCompletionCertificate : BruhatTitsCompletionCertificateStatement.{u} :=
  bruhatTitsCompletionCertificateReduction.{u}
    bruhatTitsAvailability.{u} unramifiedDescentOfGroupAxioms.{u}

end Langlands.Geometry.Building
