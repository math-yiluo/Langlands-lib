import Langlands.AlgebraicGeometry.DvrStableNormalization.AffineGeomReduced
import Langlands.AlgebraicGeometry.DvrStableNormalization.AffineHypotheses

/-! # Relative normalizations over an affine scheme over a DVR -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

namespace Langlands.AlgebraicGeometry.DvrStableNormalization

variable {R' : Type u} [CommRing R']

/-- If the integral closure of `Γ(Z)` in `Γ(W)` is finite and stays reduced after base change to
every field, then the relative normalization of an affine `Z` over `Spec R'` in `W` is finite and
geometrically reduced over `Spec R'`. -/
theorem finite_geometricallyReduced_normalization (Z : Over (Spec (CommRingCat.of R')))
    [IsAffine Z.left] {W : Scheme.{u}} (φ : W ⟶ Z.left) [QuasiCompact φ] [QuasiSeparated φ]
    (hfin : letI := (φ.app ⊤).hom.toAlgebra
      Module.Finite Γ(Z.left, ⊤) (integralClosure Γ(Z.left, ⊤) Γ(W, φ ⁻¹ᵁ ⊤)))
    (hred : letI := (φ.app ⊤).hom.toAlgebra
      letI : Algebra R' (integralClosure Γ(Z.left, ⊤) Γ(W, φ ⁻¹ᵁ ⊤)) :=
        ((algebraMap Γ(Z.left, ⊤) _).comp (globalAlgebraMap Z)).toAlgebra
      ∀ (F : Type u) [Field F] [Algebra R' F],
        IsReduced (F ⊗[R'] integralClosure Γ(Z.left, ⊤) Γ(W, φ ⁻¹ᵁ ⊤))) :
    IsFinite φ.fromNormalization ∧ GeometricallyReduced (φ.fromNormalization ≫ Z.hom) := by
  let := (φ.app ⊤).hom.toAlgebra
  have hU : IsAffineOpen (⊤ : Z.left.Opens) := isAffineOpen_top _
  let oi := φ.normalizationObjIso hU
  have happ : φ.fromNormalization.app ⊤ =
      CommRingCat.ofHom (algebraMap Γ(Z.left, ⊤)
        (integralClosure Γ(Z.left, ⊤) Γ(W, φ ⁻¹ᵁ ⊤))) ≫ oi.inv :=
    Scheme.Hom.fromNormalization_app φ hU
  have : IsAffine φ.normalization := isAffine_of_isAffineHom φ.fromNormalization
  constructor
  · rw [IsFinite.iff_isIntegralHom_and_locallyOfFiniteType]
    refine ⟨inferInstance, ?_⟩
    rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)]
    change (φ.fromNormalization.app ⊤).hom.FiniteType
    rw [happ, CommRingCat.hom_comp]
    exact ((RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso oi.inv).2).comp
      (RingHom.finite_algebraMap.mpr hfin)).finiteType
  · apply geometricallyReduced_of_isAffine
    intro F _ _
    let : Algebra R' (integralClosure Γ(Z.left, ⊤) Γ(W, φ ⁻¹ᵁ ⊤)) :=
      ((algebraMap Γ(Z.left, ⊤) _).comp (globalAlgebraMap Z)).toAlgebra
    let : Algebra R' Γ(φ.normalization, ⊤) :=
      ((φ.fromNormalization ≫ Z.hom).appTop.hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom).toAlgebra
    let e : Γ(φ.normalization, ⊤) ≃ₐ[R'] integralClosure Γ(Z.left, ⊤) Γ(W, φ ⁻¹ᵁ ⊤) :=
      { oi.commRingCatIsoToRingEquiv with
        commutes' := fun s => by
          change oi.hom ((φ.fromNormalization ≫ Z.hom).appTop
            ((Scheme.ΓSpecIso (CommRingCat.of R')).inv s)) = _
          rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
          change oi.hom ((φ.fromNormalization.app ⊤) _) = _
          rw [happ, CommRingCat.comp_apply, Iso.inv_hom_id_apply]
          rfl }
    have := hred F
    let T := Algebra.TensorProduct.congr (AlgEquiv.refl (R := R') (A₁ := F)) e
    exact isReduced_of_injective T.toRingHom T.injective

end Langlands.AlgebraicGeometry.DvrStableNormalization
