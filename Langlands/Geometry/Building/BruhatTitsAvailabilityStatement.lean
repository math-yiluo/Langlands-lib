import Langlands.Geometry.Building.FullValidity.Assignment

/-! # Bruhat–Tits theory is available for every connected reductive group -/

universe u

namespace Langlands.Geometry.Building

/-- The Definition 4.1.26 conclusion of KP Theorem 9.2.7, for corrected Definition 4.1.26
and nonarchimedean local fields: some assignment of building and integral-model data to every
connected reductive group over every nonarchimedean local field in universe `u` satisfies all
ten corrected axioms, including the comparisons of Axiom 4.1.1 and Axiom 4.1.17 between the
assigned data. Axiom 4.1.27 (unramified descent) is not part of this statement. -/
def BruhatTitsAvailabilityStatement : Prop :=
  ∃ 𝔅 : KPBuildingAssignment.{u}, 𝔅.IsValid

end Langlands.Geometry.Building
