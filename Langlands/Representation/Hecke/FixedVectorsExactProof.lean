import Langlands.Representation.Hecke.FixedVectorCornerStatements
import Langlands.Representation.Compact.ProjectionProof

/-! # Exactness of compact-open fixed vectors -/

namespace Langlands.Hecke

universe u v

/-- Renard III.1.5, Proposition (iv), by natural finite-orbit averaging. -/
theorem fixedVectorsExact : FixedVectorsExactStatement.{u, v} := by
  intro G _ _ _ _ _ _ A B C f g K hK hfg
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    apply Subtype.ext
    have hx : (SmoothRep.hom f) (x : A) ∈
        LinearMap.range (SmoothRep.hom f).toLinearMap := ⟨x, rfl⟩
    rw [hfg] at hx
    exact hx
  · intro y hy
    have hy0 : (y : B) ∈ LinearMap.ker (SmoothRep.hom g).toLinearMap :=
      congrArg Subtype.val hy
    rw [← hfg] at hy0
    obtain ⟨x, hx⟩ := hy0
    change (SmoothRep.hom f) x = (y : B) at hx
    refine ⟨⟨Compact.averageMap A.representation A.isSmooth K hK x,
      Compact.averageMap_mem_fixedVectors A.representation A.isSmooth K hK x⟩, ?_⟩
    apply Subtype.ext
    change (SmoothRep.hom f) (Compact.averageMap A.representation A.isSmooth K hK x) =
      (y : B)
    have hn := LinearMap.congr_fun
      (Compact.averageMap_commute A.representation B.representation
        A.isSmooth B.isSmooth K hK (SmoothRep.hom f)) x
    change (SmoothRep.hom f) (Compact.averageMap A.representation A.isSmooth K hK x) =
      Compact.averageMap B.representation B.isSmooth K hK ((SmoothRep.hom f) x) at hn
    rw [hn, hx]
    exact Compact.averageMap_id B.representation B.isSmooth K hK y y.property

end Langlands.Hecke
