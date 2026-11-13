import Langlands.AlgebraicGeometry.Picard.InfinitesimalGluing

/-! # Algebra maps inducing arrows between affine bases -/

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard.OpennessOfVersality

/-- Every arrow between affine bases over `Spec R` comes from an `R`-algebra homomorphism. -/
lemma exists_affineBaseMap_eq {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (b : affineBase R B ⟶ affineBase R A) :
    ∃ χ : A →ₐ[R] B, affineBaseMap χ = b := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective b.left
  have hw : b.left ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) := Over.w b
  rw [← hφ, ← Spec.map_comp] at hw
  have hcomm := congrArg CommRingCat.Hom.hom (Spec.map_injective hw)
  refine ⟨{ φ.hom with commutes' := fun r => congrArg (fun h : R →+* B => h r) hcomm }, ?_⟩
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom _) = b.left
  rw [← hφ]
  rfl

end Langlands.AlgebraicGeometry.Picard.OpennessOfVersality
