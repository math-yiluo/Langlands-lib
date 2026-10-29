import Langlands.AlgebraicGeometry.Picard.RigidifiedClassesEqualizerClosedAffineFromNoetherianStatement

/-! # Proof: the affine agreement locus from the noetherian case and noetherian approximation -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- The affine closed agreement locus follows from its noetherian case and noetherian
approximation of the agreement predicate: the closed subscheme over `Spec R` is the pullback of
the noetherian one along `Spec.map φ`. -/
theorem rigidifiedClassesEqualizerClosedAffine_of_noetherian :
    RigidifiedClassesEqualizerClosedAffineFromNoetherianStatement.{u} := by
  intro hNoeth hApprox R A q r
  obtain ⟨R₀, hR₀, φ, A₀, q₀, r₀, hiff⟩ := hApprox R A q r
  obtain ⟨Z₀, ι₀, hι₀, hZ₀⟩ := hNoeth R₀ A₀ q₀ r₀
  refine ⟨pullback ι₀ (Spec.map φ), pullback.snd ι₀ (Spec.map φ), inferInstance, ?_⟩
  intro T' h
  have hh : h.left = T'.hom := by simpa using Over.w h
  refine Iff.trans ?_ ((hZ₀ _ _).trans (hiff T' h).symm)
  simp only [Over.homMk_left, hh]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨g ≫ pullback.fst ι₀ (Spec.map φ), ?_⟩
    rw [Category.assoc, pullback.condition, ← Category.assoc, hg]
  · rintro ⟨g, hg⟩
    exact ⟨pullback.lift g T'.hom hg, pullback.lift_snd _ _ _⟩

end Langlands.AbelianScheme
