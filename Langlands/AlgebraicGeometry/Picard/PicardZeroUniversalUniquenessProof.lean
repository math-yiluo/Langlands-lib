import Langlands.AlgebraicGeometry.Picard.PicardZeroUniversalStatements

/-! # Uniqueness of universal geometric Picard-zero families -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle

/-- Two universal Picard-zero families determine a unique compatible isomorphism
of their parameter schemes, using only the stated rigidified pullback coherence. -/
theorem picardZeroUniversalUniqueness : PicardZeroUniversalUniquenessStatement.{u} := by
  intro coherence S A P Q L M hL hM
  let qL : PicardZeroClasses A P :=
    ⟨classOf A.X.hom (unitSection A) (unitSection_comp A) L, hL.1⟩
  let qM : PicardZeroClasses A Q :=
    ⟨classOf A.X.hom (unitSection A) (unitSection_comp A) M, hM.1⟩
  obtain ⟨a, ha, ua⟩ := hM.2 P qL
  obtain ⟨b, hb, _⟩ := hL.2 Q qM
  have hab : a ≫ b = 𝟙 P := by
    apply (hL.2 P qL).unique
    · rw [classifyingMap_comp A.X.hom (unitSection A) (unitSection_comp A)
        coherence L a b, hb]
      exact ha
    · exact classifyingMap_id A.X.hom (unitSection A) (unitSection_comp A)
        coherence L
  have hba : b ≫ a = 𝟙 Q := by
    apply (hM.2 Q qM).unique
    · rw [classifyingMap_comp A.X.hom (unitSection A) (unitSection_comp A)
        coherence M b a, ha]
      exact hb
    · exact classifyingMap_id A.X.hom (unitSection A) (unitSection_comp A)
        coherence M
  refine ⟨⟨a, b, hab, hba⟩, ?_, ?_⟩
  · exact (classifyingMap_eq_iff A.X.hom (unitSection A) (unitSection_comp A)
      M L a).mp ha
  · intro e he
    apply Iso.ext
    exact ua e.hom ((classifyingMap_eq_iff A.X.hom (unitSection A)
      (unitSection_comp A) M L e.hom).mpr he)

end Langlands.AbelianScheme
