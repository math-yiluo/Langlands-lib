import Langlands.Group.GL.Padic
import Langlands.Group.GL.OppositeBlocks
import Langlands.Representation.Geometric.GeneralCorrectionCharacters

/-! Actual positive Haar correction cancellation for p-adic GL parabolic orbits. -/

namespace Langlands.Geometric

universe uF

/-- The two actual positive Haar corrections cancel after transporting the second
by the published intersection-Levi conjugation equivalence. This is a proposition
definition for Bernstein--Zelevinsky (1977), section 6.4, not its proof. -/
def PadicHaarCorrectionCancellation : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ), 0 < n →
    ∀ (B C : GeneralLinear.BlockShape n) (w : MinimalRepresentatives B C),
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI := T.generalLinearLocallyCompactSpace n
    let M := B.leviSubgroup F.Carrier
    let N := C.leviSubgroup F.Carrier
    let U := B.unipotentSubgroup F.Carrier
    let V := C.unipotentSubgroup F.Carrier
    let P := B.parabolic F.Carrier
    let Q := C.parabolic F.Carrier
    let g := GeneralLinear.permutation n F.Carrier w.val
    let hU := B.isClosed_unipotentSubgroup F.Carrier
    let hV := C.isClosed_unipotentSubgroup F.Carrier
    let hP := B.isClosed_parabolic F.Carrier
    let hQ := C.isClosed_parabolic F.Carrier
    let hMU := B.leviSubgroup_le_normalizer_unipotentSubgroup F.Carrier
    let hNV := C.leviSubgroup_le_normalizer_unipotentSubgroup F.Carrier
    let hNQ : N ≤ Subgroup.normalizer Q := fun x hx =>
      Q.le_normalizer (C.leviAsParabolic F.Carrier ⟨x, hx⟩).property
    let hMP : M ≤ Subgroup.normalizer P := fun x hx =>
      P.le_normalizer (B.leviAsParabolic F.Carrier ⟨x, hx⟩).property
    ∀ m : General.intersectionIn M N g,
      General.haarCorrectionCharacter M N U Q g hU hQ hMU hNQ m *
        General.haarCorrectionCharacter N M V P g⁻¹ hV hP hNV hMP
          (General.intersectionEquiv M N g m) = 1

end Langlands.Geometric
