import Langlands.AlgebraicGeometry.FiniteSeparableGenericCoverStatement
import Langlands.AlgebraicGeometry.FiniteSeparableGenericCoverData

/-! # Realizing a prescribed finite separable generic extension -/

universe u

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

/-- The constructed generic cover satisfies the exact prescribed-cover statement. -/
theorem finiteSeparableGenericCover : FiniteSeparableGenericCover.{u} := by
  intro Y _ η hη L _ _ _ _
  let d := PrescribedGenericCoverData.construct η hη L
  exact ⟨d.baseOpen, d.baseOpen_nonempty, d.model, d.cover,
    d.affine, d.irreducible, d.surjective, d.finite, d.etale,
    d.generic, d.isGenericPoint, d.residueIso, d.triangle⟩

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
