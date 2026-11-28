import Langlands.Representation.Exponents.CasselmanFromBuildingProof
import Langlands.Geometry.Building.BruhatTitsAvailabilityProof

/-! # Proof of Casselman's criterion for actual rational parabolics

Renard 2026, VII.1.2 (printed pp.221–224/PDF pp.227–230), in the formulation
`ArbitraryParabolicCasselmanCriterionStatement` (strictly positive root cone,
`q^(-s)` real part). The building premise of `casselmanFromBuilding` is discharged
by the Bruhat–Tits availability theorem `bruhatTitsAvailability`.
-/

universe u v

namespace Langlands.Aubert.General.RepresentedParabolic

/-- Renard VII.1.2 (Casselman's criterion): for a connected reductive group over a
nonarchimedean local field, a Haar measure on `G(k) ⧸ Z(G(k))` and an admissible
smooth complex representation with a unitary central character, square integrability
modulo the center is equivalent to the normalized real part of every normalized
Jacquet exponent, for every actual rational parabolic with compatible root
presentation, lying in the strictly positive root cone. -/
theorem arbitraryParabolicCasselmanCriterion :
    ArbitraryParabolicCasselmanCriterionStatement.{u, v} :=
  casselmanFromBuilding.{u, v} Langlands.Geometry.Building.bruhatTitsAvailability.{u}

end Langlands.Aubert.General.RepresentedParabolic
