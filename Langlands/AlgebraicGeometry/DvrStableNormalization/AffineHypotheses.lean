import Langlands.AlgebraicGeometry.DvrStableNormalization.GenericFibre

/-! # Ring-level hypotheses for affine schemes over a DVR -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

namespace Langlands.AlgebraicGeometry.DvrStableNormalization

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The `R`-algebra structure on the global sections of a scheme over `Spec R`. -/
abbrev globalAlgebraMap (Z : Over (Spec (CommRingCat.of R))) : R →+* Γ(Z.left, ⊤) :=
  Z.hom.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem flat_globalAlgebraMap (Z : Over (Spec (CommRingCat.of R))) [IsAffine Z.left]
    [Flat Z.hom] : (globalAlgebraMap Z).Flat := by
  have h : Z.hom.appTop.hom.Flat := HasRingHomProperty.appTop @Flat Z.hom ‹_›
  exact RingHom.Flat.comp (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _)) h

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem finiteType_globalAlgebraMap (Z : Over (Spec (CommRingCat.of R))) [IsAffine Z.left]
    [LocallyOfFiniteType Z.hom] : (globalAlgebraMap Z).FiniteType := by
  have h : Z.hom.appTop.hom.FiniteType := HasRingHomProperty.appTop @LocallyOfFiniteType Z.hom ‹_›
  exact h.comp (RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso _).2)

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- The generic fibre of the global sections of an affine scheme with smooth generic fibre is
smooth over the fraction field. -/
theorem smooth_globalAlgebraMap (Z : Over (Spec (CommRingCat.of R))) [IsAffine Z.left]
    [Smooth (pullback.snd Z.hom (Spec.algebraMap R (FractionRing R)))] :
    letI := (globalAlgebraMap Z).toAlgebra
    Algebra.Smooth (FractionRing R) (FractionRing R ⊗[R] Γ(Z.left, ⊤)) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  let := (globalAlgebraMap Z).toAlgebra
  have hK := isLocalizationAway_fractionRing_of_dvr R (FractionRing R) hϖ
  let := ((genericι Z).app ⊤).hom.toAlgebra
  have hL : IsLocalization.Away (resSec Z ϖ ⊤)
      Γ(pullback Z.hom (Spec.algebraMap R (FractionRing R)), (genericι Z) ⁻¹ᵁ ⊤) :=
    isLocalization_genericι_app Z hϖ (isAffineOpen_top _)
  have hres : resSec Z ϖ ⊤ = algebraMap R Γ(Z.left, ⊤) ϖ := by
    change Z.left.presheaf.map (homOfLE le_top : (⊤ : Z.left.Opens) ⟶ ⊤).op _ = _
    rw [show (homOfLE le_top : (⊤ : Z.left.Opens) ⟶ ⊤) = 𝟙 _ from rfl, op_id,
      Z.left.presheaf.map_id]
    rfl
  rw [hres] at hL
  have hT : IsLocalization.Away (algebraMap R Γ(Z.left, ⊤) ϖ)
      (FractionRing R ⊗[R] Γ(Z.left, ⊤)) := IsLocalization.Away.tensorRight ..
  let e : FractionRing R ⊗[R] Γ(Z.left, ⊤) ≃ₐ[Γ(Z.left, ⊤)]
      Γ(pullback Z.hom (Spec.algebraMap R (FractionRing R)), (genericι Z) ⁻¹ᵁ ⊤) :=
    IsLocalization.algEquiv (Submonoid.powers (algebraMap R Γ(Z.left, ⊤) ϖ)) _ _
  let eK := Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))
  let ψ : FractionRing R →+*
      Γ(pullback Z.hom (Spec.algebraMap R (FractionRing R)), (genericι Z) ⁻¹ᵁ ⊤) :=
    (pullback.snd Z.hom (Spec.algebraMap R (FractionRing R))).appTop.hom.comp eK.inv.hom
  have hψ : ψ.Smooth := by
    have h : (pullback.snd Z.hom (Spec.algebraMap R (FractionRing R))).appTop.hom.Smooth :=
      HasRingHomProperty.appTop @Smooth _ ‹_›
    exact RingHom.Smooth.comp (RingHom.Smooth.of_bijective
      (ConcreteCategory.bijective_of_isIso _)) h
  have hlin : e.toRingHom.comp Algebra.TensorProduct.includeLeftRingHom = ψ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers ϖ)
    ext r
    simp only [RingHom.comp_apply, Algebra.TensorProduct.includeLeftRingHom_apply]
    have h1 : algebraMap R (FractionRing R) r ⊗ₜ[R] (1 : Γ(Z.left, ⊤)) =
        algebraMap Γ(Z.left, ⊤) (FractionRing R ⊗[R] Γ(Z.left, ⊤))
          (algebraMap R Γ(Z.left, ⊤) r) := by
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one (A := Γ(Z.left, ⊤)),
        TensorProduct.smul_tmul]
      rfl
    rw [h1]
    change e (algebraMap _ _ _) = _
    rw [e.commutes]
    have hnat := congrArg (fun h => h r) (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (algebraMap R (FractionRing R))))
    change eK.inv (algebraMap R (FractionRing R) r) =
      (Spec.algebraMap R (FractionRing R)).appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)
      at hnat
    change ((genericι Z).appTop) (Z.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)) =
      (pullback.snd Z.hom (Spec.algebraMap R (FractionRing R))).appTop
        (eK.inv (algebraMap R (FractionRing R) r))
    rw [hnat]
    have hc := congrArg (fun h => Scheme.Hom.appTop h)
      (pullback.condition (f := Z.hom) (g := Spec.algebraMap R (FractionRing R)))
    simp only [Scheme.Hom.comp_appTop] at hc
    exact congrArg (fun h => h ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)) hc
  let := ψ.toAlgebra
  have : Algebra.Smooth (FractionRing R)
      Γ(pullback Z.hom (Spec.algebraMap R (FractionRing R)), (genericι Z) ⁻¹ᵁ ⊤) := hψ
  let e' : FractionRing R ⊗[R] Γ(Z.left, ⊤) ≃ₐ[FractionRing R]
      Γ(pullback Z.hom (Spec.algebraMap R (FractionRing R)), (genericι Z) ⁻¹ᵁ ⊤) :=
    { e.toRingEquiv with
      commutes' := fun k => by
        change e (k ⊗ₜ[R] 1) = ψ k
        rw [← hlin]
        rfl }
  exact Algebra.Smooth.of_equiv e'.symm

end Langlands.AlgebraicGeometry.DvrStableNormalization
