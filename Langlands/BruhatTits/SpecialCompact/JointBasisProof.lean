import Langlands.BruhatTits.SpecialCompact.JointBasisFinalAssembly
import Langlands.BruhatTits.SpecialCompact.AvailableBasisProof
import Langlands.Geometry.Building.BruhatTitsAvailabilityProof

/-! # A common geometric witness for the special compact and simultaneous basis -/

universe u

namespace Langlands.BruhatTits.SpecialCompact

/-- Renard V.5.1–V.5.2 at one geometric special vertex: for every nonarchimedean
local field, connected reductive group, maximal split torus and generic
cocharacter, one apartment datum, one point and one represented torus
centralizer with its character comparison satisfy the special compact
properties, standard-Levi inheritance, ambient and Levi Iwasawa products,
ambient and Levi Cartan comparisons and the simultaneous standard basis. -/
theorem jointSpecialCompactBasisExistence :
    JointSpecialCompactBasisExistenceStatement.{u} :=
  jointSpecialCompactBasisExistence_of_availability_and_basis
    Langlands.Geometry.Building.bruhatTitsAvailability
    availableSimultaneousStandardBasis

end Langlands.BruhatTits.SpecialCompact
