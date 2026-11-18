import Mathlib

/-! # Geometric reducedness of affine schemes from their global sections -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

namespace Langlands.AlgebraicGeometry.DvrStableNormalization

/-- An affine scheme over `Spec R'` whose global sections stay reduced after base change to every
field is geometrically reduced over `Spec R'`. -/
theorem geometricallyReduced_of_isAffine {R' : Type u} [CommRing R'] {Y : Scheme.{u}} [IsAffine Y]
    (f : Y ⟶ Spec (CommRingCat.of R'))
    (h : letI := (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom).toAlgebra
      ∀ (F : Type u) [Field F] [Algebra R' F], IsReduced (F ⊗[R'] Γ(Y, ⊤))) :
    GeometricallyReduced f := by
  let φ : CommRingCat.of R' ⟶ Γ(Y, ⊤) := (Scheme.ΓSpecIso _).inv ≫ f.appTop
  let := φ.hom.toAlgebra
  have hf : f = Y.isoSpec.hom ≫ Spec.map φ := by
    have := Scheme.isoSpec_hom_naturality f
    rw [Scheme.isoSpec_Spec_hom] at this
    rw [Spec.map_comp, ← Category.assoc, this, Category.assoc, ← Spec.map_comp, Iso.inv_hom_id,
      Spec.map_id, Category.comp_id]
  constructor
  intro K _ y Z fst snd hpb
  obtain ⟨ρ, rfl⟩ := Spec.map_surjective y
  let := ρ.hom.toAlgebra
  have t : IsPullback Y.isoSpec.hom f (Spec.map φ) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, hf]⟩
  have hpb' : IsPullback (fst ≫ Y.isoSpec.hom) snd (Spec.map φ) (Spec.map ρ) := by
    simpa using hpb.paste_horiz t
  have hR : _root_.IsReduced (Γ(Y, ⊤) ⊗[R'] K) := by
    have := h K
    exact isReduced_of_injective (Algebra.TensorProduct.comm R' Γ(Y, ⊤) K).toRingHom
      (Algebra.TensorProduct.comm R' Γ(Y, ⊤) K).injective
  let e : Z ≅ Spec (CommRingCat.of (Γ(Y, ⊤) ⊗[R'] K)) :=
    hpb'.isoPullback ≪≫ pullbackSpecIso R' Γ(Y, ⊤) K
  exact isReduced_of_isOpenImmersion e.hom

end Langlands.AlgebraicGeometry.DvrStableNormalization
