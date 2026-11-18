import Langlands.AlgebraicGeometry.RelativeQuasiAffineDescentStatement
import Langlands.AlgebraicGeometry.QuasiAffineEtaleDescent

/-! # Relative quasi-affineness descends along a flat quasi-compact surjection -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- Quasi-affineness descends along a flat, quasi-compact, surjective base change. -/
theorem relativeQuasiAffineFlatDescent : RelativeQuasiAffineFlatDescentStatement.{u} := by
  intro X S S' f p _ _ _ h V
  have : IsAffine V.1.toScheme := V.2
  let fV : (f ⁻¹ᵁ V.1).toScheme ⟶ V.1.toScheme := f ∣_ V.1
  have : CompactSpace (p ⁻¹ᵁ V.1).toScheme :=
    QuasiCompact.compactSpace_of_compactSpace (p ∣_ V.1)
  have : Surjective (p ∣_ V.1) :=
    IsZariskiLocalAtTarget.restrict (P := @Surjective) inferInstance V.1
  let 𝒰 := (p ⁻¹ᵁ V.1).toScheme.affineCover.finiteSubcover
  let q (i : 𝒰.I₀) : 𝒰.X i ⟶ V.1.toScheme := 𝒰.f i ≫ p ∣_ V.1
  have : Finite 𝒰.I₀ := by infer_instance
  have (i : 𝒰.I₀) : IsAffine (𝒰.X i) := by
    dsimp only [𝒰, Scheme.OpenCover.finiteSubcover_X]
    infer_instance
  have (i : 𝒰.I₀) : Flat (q i) := by
    dsimp only [q]
    infer_instance
  have (i : 𝒰.I₀) : (pullback fV (q i)).IsQuasiAffine := by
    let b : 𝒰.X i ⟶ S' := 𝒰.f i ≫ (p ⁻¹ᵁ V.1).ι
    have : IsOpenImmersion b := by
      dsimp only [b]
      infer_instance
    have : (pullback f (b ≫ p)).IsQuasiAffine :=
      QuasiAffineEtaleDescent.isQuasiAffine_pullback_affine_open f p h b
    have hb := (IsPullback.of_hasPullback fV (q i)).paste_horiz
      (isPullback_morphismRestrict f V.1).flip
    have hq : q i ≫ V.1.ι = b ≫ p := by
      simp only [q, b, Category.assoc, morphismRestrict_ι]
    rw [hq] at hb
    exact Scheme.IsQuasiAffine.of_isAffineHom hb.isoPullback.hom
  apply QuasiAffineCoverDescent.isQuasiAffine_of_finite_affine_cover fV 𝒰.X q
  intro s
  obtain ⟨s', rfl⟩ := (p ∣_ V.1).surjective s
  obtain ⟨i, x, rfl⟩ := 𝒰.exists_eq s'
  exact ⟨i, x, Scheme.Hom.comp_apply _ _ _⟩

end Langlands.AlgebraicGeometry
