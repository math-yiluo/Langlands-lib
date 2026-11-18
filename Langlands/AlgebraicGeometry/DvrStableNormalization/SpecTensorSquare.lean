import Langlands.AlgebraicGeometry.DvrStableNormalization.CoverBaseChange

/-! # Base change of an affine scheme over a DVR as the spectrum of a tensor product -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

namespace Langlands.AlgebraicGeometry.DvrStableNormalization

variable {R : Type u} [CommRing R] (Zo : Over (Spec (CommRingCat.of R))) [IsAffine Zo.left]
  (R' : Type u) [CommRing R'] [Algebra R R']

/-- The structure morphism of an affine scheme over `Spec R` is `Spec` of its algebra map,
up to the canonical isomorphism with the spectrum of the global sections. -/
lemma hom_eq_isoSpec_comp :
    letI := (Zo.hom.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).toAlgebra
    Zo.hom = Zo.left.isoSpec.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap R Γ(Zo.left, ⊤))) := by
  let φ : CommRingCat.of R ⟶ Γ(Zo.left, ⊤) := (Scheme.ΓSpecIso _).inv ≫ Zo.hom.appTop
  have := Scheme.isoSpec_hom_naturality Zo.hom
  rw [Scheme.isoSpec_Spec_hom] at this
  change Zo.hom = Zo.left.isoSpec.hom ≫ Spec.map φ
  rw [Spec.map_comp, ← Category.assoc, this, Category.assoc, ← Spec.map_comp, Iso.inv_hom_id,
    Spec.map_id, Category.comp_id]

/-- The spectrum of `R' ⊗[R] Γ(Zo)` is the base change of `Zo` along `Spec R' → Spec R`. -/
theorem isPullback_spec_tensor :
    letI := (Zo.hom.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).toAlgebra
    IsPullback
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        Γ(Zo.left, ⊤) →ₐ[R] R' ⊗[R] Γ(Zo.left, ⊤)).toRingHom) ≫ Zo.left.isoSpec.inv)
      (Spec.map (CommRingCat.ofHom (algebraMap R' (R' ⊗[R] Γ(Zo.left, ⊤)))))
      Zo.hom (Spec.map (CommRingCat.ofHom (algebraMap R R'))) := by
  let := (Zo.hom.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).toAlgebra
  have hf := hom_eq_isoSpec_comp Zo
  have h0 : IsPullback (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
        R' →+* R' ⊗[R] Γ(Zo.left, ⊤))))
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        Γ(Zo.left, ⊤) →ₐ[R] R' ⊗[R] Γ(Zo.left, ⊤)).toRingHom))
      (Spec.map (CommRingCat.ofHom (algebraMap R R')))
      (Spec.map (CommRingCat.ofHom (algebraMap R Γ(Zo.left, ⊤)))) :=
    IsPullback.of_iso_pullback ⟨by
        rw [← Spec.map_comp, ← Spec.map_comp]
        congr 1
        ext x
        simp [Algebra.TensorProduct.tmul_one_eq_one_tmul]⟩
      (pullbackSpecIso R R' Γ(Zo.left, ⊤)).symm
      (pullbackSpecIso_inv_fst R R' Γ(Zo.left, ⊤))
      (pullbackSpecIso_inv_snd R R' Γ(Zo.left, ⊤))
  have t : IsPullback Zo.left.isoSpec.inv
      (Spec.map (CommRingCat.ofHom (algebraMap R Γ(Zo.left, ⊤)))) Zo.hom (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, hf, Iso.inv_hom_id_assoc]⟩
  have := h0.flip.paste_horiz t
  simpa using this

end Langlands.AlgebraicGeometry.DvrStableNormalization
