import Langlands.AlgebraicGeometry.Picard.FieldBaseChangeAmpleStatement
import Langlands.AlgebraicGeometry.Picard.ClosedImmersionPullbackAmpleProof
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Preservation of ampleness under field base change -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

set_option backward.isDefEq.respectTransparency.types false in
/-- Actual pullback of an ample line bundle along field base change is ample. -/
theorem fieldBaseChangeAmple : FieldBaseChangeAmpleStatement.{u} := by
  intro k K _ _ b X p L hL
  let q := CategoryTheory.Limits.pullback.fst p b
  let : IsAffineHom b := inferInstance
  let : IsAffineHom q := MorphismProperty.pullback_fst p b (inferInstance : IsAffineHom b)
  let : CompactSpace X := hL.1
  refine ⟨QuasiCompact.compactSpace_of_compactSpace q, ?_⟩
  intro x
  obtain ⟨n, hn, s, hx, ha⟩ := hL.2 (q x)
  let s' := L.pullbackPowSection q s
  have hopen :
      ((LineBundle.pullback q).obj L).sectionOpen s' = q ⁻¹ᵁ L.sectionOpen s :=
    LineBundle.sectionOpen_pullbackPowSection q L s
  refine ⟨n, hn, s', ?_, ?_⟩
  · rw [hopen]
    exact hx
  · rw [hopen]
    exact ha.preimage q

end Langlands.AlgebraicGeometry.Picard
