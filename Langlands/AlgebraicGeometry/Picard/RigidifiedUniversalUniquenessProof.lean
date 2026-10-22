import Langlands.AlgebraicGeometry.Picard.RigidifiedUniversalStatements

/-! # Uniqueness of universal rigidified line bundles -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle

/-- Universal rigidified families determine a unique compatible isomorphism of
parameter schemes, assuming the stated pullback coherence. -/
theorem universalBundleUniqueness : UniversalBundleUniquenessStatement.{u} := by
  intro coherence S X f ε section_eq P Q L M hL hM
  obtain ⟨a, ha⟩ := (hM P).surjective (classOf f ε section_eq L)
  obtain ⟨b, hb⟩ := (hL Q).surjective (classOf f ε section_eq M)
  have hab : a ≫ b = 𝟙 P := by
    apply (hL P).injective
    rw [classifyingMap_comp f ε section_eq coherence L a b, hb]
    change classifyingMap f ε section_eq M P a = _
    rw [ha, classifyingMap_id f ε section_eq coherence L]
  have hba : b ≫ a = 𝟙 Q := by
    apply (hM Q).injective
    rw [classifyingMap_comp f ε section_eq coherence M b a, ha]
    change classifyingMap f ε section_eq L Q b = _
    rw [hb, classifyingMap_id f ε section_eq coherence M]
  refine ⟨⟨a, b, hab, hba⟩, ?_, ?_⟩
  · exact (classifyingMap_eq_iff f ε section_eq M L a).mp ha
  · intro e he
    apply Iso.ext
    exact (hM P).injective
      (((classifyingMap_eq_iff f ε section_eq M L e.hom).mpr he).trans ha.symm)

end Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle
