import Langlands.Representation.Hecke.FixedVectorCornerStatements
import Langlands.Representation.Hecke.CornerDetermination

/-! # Irreducible representations determined by their fixed corner modules -/

noncomputable section

namespace Langlands.Hecke

open MeasureTheory

universe u v

/-- Renard III.1.5, Theorem (ii), using the corner-annihilator determination theorem. -/
theorem irreducibleEquivIffFixedEquiv : IrreducibleEquivIffFixedEquivStatement.{u, v} := by
  intro G _ _ _ _ _ _ _ _ μ _ A B hA hB K hK hKA hKB
  let _ := cornerModule μ A.representation A.isSmooth K hK
  let _ := cornerModule μ B.representation B.isSmooth K hK
  constructor
  · rintro ⟨e⟩
    exact ⟨{
      toAddEquiv := (fixedVectorsEquiv e K.toSubgroup).toAddEquiv
      map_smul' := fun f w =>
        cornerAction_equiv μ A.representation A.isSmooth K hK B.isSmooth e f w }⟩
  · rintro ⟨e⟩
    obtain ⟨a, haK, ha⟩ := (Submodule.ne_bot_iff _).mp hKA
    let aK : fixedVectors A.representation K.toSubgroup := ⟨a, haK⟩
    have haK0 : aK ≠ 0 := fun h => ha (congrArg Subtype.val h)
    have hb : (e aK : B) ≠ 0 := by
      intro h
      have h' : e aK = 0 := Subtype.ext h
      exact haK0 (e.injective (h'.trans e.map_zero.symm))
    apply nonempty_equiv_of_cornerAction_eq_zero_iff μ K hK
      A.isSmooth hA B.isSmooth hB aK (e aK) ha hb
    intro f
    change f • aK = 0 ↔ f • e aK = 0
    rw [← e.map_smul]
    exact e.map_eq_zero_iff.symm

end Langlands.Hecke
